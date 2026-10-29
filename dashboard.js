/* ═══════════════════════════════════════════════════════════
   POLPO :: NETWORK ANALYZER  ·  dashboard.js
   Toda la lógica de visualización (D3 + grafo + interacción).
   No conoce Supabase: solo recibe rows transformados desde app.js
   y dibuja. Entry point: buildDashboard(rows, extras).
   -bynd

   v3 · grafo tipo instagram
   ─────────────────────────
   Antes el grafo era un árbol origen → user → user (cada nodo
   tenía UN solo padre: su origen de cacheo). Ahora hay dos tipos
   de arista y un nodo puede tener varios "padres":

     follows  A ──▶ B   A sigue a B. Sale de la tabla followed_by
                        (el "Followed by A, C + 3 more" que lee el
                        bot en el perfil de B). Varios usuarios
                        convergen en uno, como en instagram.
     origen   O ┄┄▶ U   U se cacheó desde la lista de O (linaje
                        del bot). Se sigue usando para dead families.

   Redes infiltradas
   ─────────────────
   Sobre el grafo completo (follows pesa más que origen) se corre
   Louvain → comunidades. Para cada red con ≥ 3 nodos se mide:
     index = (0.6·mutuals + 0.4·sigues) / tamaño        (0 … 1)
   y se clasifica:
     INFILTRATED  ≥ 2 mutuals  y  index ≥ 0.35
     CONTACT      ≥ 1 mutual   o  index ≥ 0.20
     COLD         lo demás
   Cada red se dibuja como un casco (hull) detrás de sus nodos.

   Constelaciones (layout)
   ───────────────────────
   Cada comunidad de Louvain es un CUERPO: un disco con radio
   proporcional a √miembros. Una fuerza propia (forceConstellations)
     · cohesión  → jala a cada nodo al centro de su cuerpo
     · colisión  → dos cuerpos no se pueden encimar (radio + gap)
     · repulsión → los cuerpos se empujan entre sí a distancia
   Las aristas ENTRE cuerpos son largas y flojas para que un puente
   no arrastre a dos constelaciones encima una de la otra. El slider
   SEPARACIÓN de la toolbar escala gap y repulsión en vivo.

   Puentes entre constelaciones
   ────────────────────────────
     · cuerpos conectados se ATRAEN (resorte ∝ log de # de aristas
       entre ellos) → redes relacionadas quedan vecinas, las demás
       se siguen repeliendo
     · PUENTE   = nodo con alguna conexión afuera de su cuerpo →
                  se acomoda en la orilla, del lado de sus vecinos
                  externos
     · SATÉLITE = nodo con tantas o más conexiones afuera que
                  adentro → sale de su cuerpo y flota en el hueco
                  hacia esos vecinos, dentro de un globito del
                  color de su red
   ═══════════════════════════════════════════════════════════ */

"use strict";

// ─── CONFIG VISUAL ───────────────────────────────────────
const DEAD_COLOR = '#B14DFF';
const TIER = {
  infiltrated: { label: 'INFILTRATED', color: '#E8FF00' },
  contact:     { label: 'CONTACT',     color: '#FF00B3' },
  cold:        { label: 'COLD',        color: '#666666' },
};
const MIN_NET_SIZE = 3;                 // redes más chicas = nodos sueltos
const EDGE_WEIGHT = { follows: 1.0, origen: 0.5 };
const DEAD_STATUSES = new Set(['unfollowed', 'inactive', 'request_cancelled']);

// ey fisica de constelaciones (SEPARACIÓN multiplica gap y repulsion) -bynd
const CONST = {
  bodyBase: 18,        // radio minimo de un cuerpo
  bodyPerNode: 15,     // radio extra por √miembro
  gap: 110,            // espacio libre entre bordes de dos redes grandes
  cohesion: 0.12,      // jalon de cada nodo al centro de su cuerpo
  collide: 0.9,        // que tan duro se separan cuerpos encimados
  repulsion: 1600,     // empuje a distancia entre cuerpos (∝ √masas / d)
  bridgeDist: 220,     // largo de aristas entre cuerpos distintos
  bridgeStrength: 0.02,
  bodySpring: 0.07,    // atraccion entre cuerpos conectados
  rimPull: 0.25,       // que tan fuerte se va un puente a la orilla
  satPull: 0.18,       // jalon del satelite a su punto afuera del cuerpo
  satOut: 0.55,        // que tan lejos sale el satelite (fraccion del gap)
  separation: 1,       // slider
};

// Un nodo está VIVO si: status === 'active'  OR  mutual === true.
// Una FAMILIA MUERTA es un sub-árbol (por aristas de ORIGEN) donde NINGÚN
// descendiente está vivo. Se pintan en morado los descendientes (y el
// origen si tampoco está vivo).
function isAlive(n) {
  if (!n) return false;
  return n.status === 'active' || n.mutual === true;
}
// ey "tuyo" = lo sigues (bot o fuera del bot) -bynd
function isYours(n) {
  return !!n && (n.mutual || n.status === 'active' || n.kind === 'external');
}

// ─── STATE ───────────────────────────────────────────────
const state = {
  nodes: [],
  links: [],
  nodeMap: new Map(),
  adj: new Map(),          // no dirigido, todas las aristas (path, componentes)
  outAdj: new Map(),       // ORIGEN: origen → spawned
  inAdj: new Map(),        // ORIGEN: spawned ← origen
  followOut: new Map(),    // FOLLOWS: A sigue a →
  followIn: new Map(),     // FOLLOWS: lo siguen ←
  deadSet: new Set(),
  nets: [],                // redes (≥ MIN_NET_SIZE), ordenadas por index
  netOf: new Map(),        // nodeId → net
  groupOf: new Map(),      // nodeId → key de cuerpo (todas, incl. sueltos)
  bodies: [],              // [{ key, ids, net }]
  roles: new Map(),        // nodeId → 'bridge' | 'satellite' (core no se guarda)
  focusNet: null,
  filter: 'all',
  selectedId: null,
  pathIds: new Set(),
  pathOrdered: [],
  showLabels: true,
  showOrigen: true,
  showFollows: true,
  showHulls: true,
  colorMode: 'status',     // 'status' | 'network'
  frozen: false,
  hasFollowData: false,
};

// ─── BUILD GRAPH FROM ROWS ───────────────────────────────
// kind: tracked (stand_users) · seen (perfil evaluado, no lo sigues)
//       external (lo sigues fuera del bot) · origin (solo origen)
const KIND_RANK = { origin: 0, external: 1, seen: 2, tracked: 3 };

function buildGraph(rows, followedBy, redRows) {
  const nodeMap = new Map();

  const ensureNode = (id, kind) => {
    if (!id) return null;
    let n = nodeMap.get(id);
    if (!n) {
      n = {
        id, username: id, kind,
        ghost: kind === 'origin',
        status: kind === 'tracked' ? 'unknown' : kind,
        mutual: false, origen: '',
        followed_at: '', mutual_checked_at: '', unfollowed_at: '', last_updated: '',
        profile_followers: '', profile_following: '', profile_ratio: '',
        stand_type: '', request_state: '', is_private: null,
        red: null,
      };
      nodeMap.set(id, n);
    } else if (KIND_RANK[kind] > KIND_RANK[n.kind]) {
      // aaa sube de categoria (ej: era origen fantasma y resulta q lo sigues) -bynd
      n.kind = kind;
      n.ghost = false;
      if (kind !== 'tracked') n.status = kind;
    }
    return n;
  };

  // links por llave dirigida; una misma pareja puede ser follows Y origen
  const linkMap = new Map();
  const addLink = (s, t, type) => {
    if (!s || !t || s === t) return;
    const k = `${s}|${t}`;
    let l = linkMap.get(k);
    if (!l) { l = { source: s, target: t, types: new Set() }; linkMap.set(k, l); }
    l.types.add(type);
  };

  // 1. stand_users → nodos tracked + aristas de origen
  rows.forEach(row => {
    const u = (row.username || '').trim();
    if (!u) return;
    const node = ensureNode(u, 'tracked');
    Object.assign(node, {
      kind: 'tracked',
      ghost: false,
      followed_at: row.followed_at || '',
      status: (row.status || 'unknown').toLowerCase(),
      mutual: row.mutual === true || String(row.mutual || '').toLowerCase() === 'true',
      mutual_checked_at: row.mutual_checked_at || '',
      unfollowed_at: row.unfollowed_at || '',
      last_updated: row.last_updated || '',
      origen: (row.origen || '').trim(),
      profile_followers: row.profile_followers ?? '',
      profile_following: row.profile_following ?? '',
      profile_ratio: row.profile_ratio ?? '',
      stand_type: row.stand_type || '',
      request_state: row.request_state || '',
      is_private: row.is_private ?? null,
    });

    const o = node.origen;
    if (o && o.toLowerCase() !== 'unknown' && o !== u) {
      ensureNode(o, 'origin');
      addLink(o, u, 'origen');
    }
  });

  // 2. followed_by → aristas follows (connection sigue a username)
  (followedBy || []).forEach(r => {
    const target = (r.username || '').trim();
    const src = (r.connection || '').trim();
    if (!target || !src) return;
    ensureNode(target, 'seen');
    ensureNode(src, 'external');   // toda connection es alguien que TÚ sigues
    addLink(src, target, 'follows');
  });

  // 3. red_perfil → score por nodo (solo si el nodo existe)
  (redRows || []).forEach(r => {
    const n = nodeMap.get((r.username || '').trim());
    if (n) n.red = r;
  });

  const links = Array.from(linkMap.values()).map(l => ({
    source: l.source,
    target: l.target,
    types: l.types,
    kind: l.types.has('follows') ? 'follows' : 'origen',
  }));

  return { nodes: Array.from(nodeMap.values()), links };
}

// ─── ADJACENCY ───────────────────────────────────────────
function indexGraph(nodes, links) {
  const mk = () => new Map(nodes.map(n => [n.id, new Set()]));
  const adj = mk(), outAdj = mk(), inAdj = mk(), followOut = mk(), followIn = mk();
  const nodeMap = new Map(nodes.map(n => [n.id, n]));

  links.forEach(l => {
    const s = l.source.id || l.source;
    const t = l.target.id || l.target;
    adj.get(s)?.add(t);
    adj.get(t)?.add(s);
    if (l.types.has('origen')) { outAdj.get(s)?.add(t); inAdj.get(t)?.add(s); }
    if (l.types.has('follows')) { followOut.get(s)?.add(t); followIn.get(t)?.add(s); }
  });
  return { adj, outAdj, inAdj, followOut, followIn, nodeMap };
}

function linkBetween(a, b) {
  return state.links.filter(l => {
    const s = l.source.id || l.source, t = l.target.id || l.target;
    return (s === a && t === b) || (s === b && t === a);
  });
}

// ─── DEAD FAMILY DETECTION (solo aristas de origen) ──────
function getAllDescendants(nodeId, outAdj) {
  const desc = new Set();
  const queue = [...(outAdj.get(nodeId) || [])];
  while (queue.length) {
    const x = queue.shift();
    if (desc.has(x)) continue;
    desc.add(x);
    outAdj.get(x)?.forEach(c => { if (!desc.has(c)) queue.push(c); });
  }
  return desc;
}

function computeDeadFamilies() {
  const dead = new Set();
  state.nodes.forEach(n => {
    const descendants = getAllDescendants(n.id, state.outAdj);
    if (descendants.size === 0) return;
    for (const dId of descendants) if (isAlive(state.nodeMap.get(dId))) return;
    descendants.forEach(d => dead.add(d));
    if (!isAlive(n)) dead.add(n.id);
  });
  return dead;
}

function connectedComponents(nodes, adj) {
  const seen = new Set();
  let count = 0;
  for (const n of nodes) {
    if (seen.has(n.id)) continue;
    count++;
    const stack = [n.id];
    while (stack.length) {
      const x = stack.pop();
      if (seen.has(x)) continue;
      seen.add(x);
      adj.get(x)?.forEach(y => { if (!seen.has(y)) stack.push(y); });
    }
  }
  return count;
}

// ─── LOUVAIN (comunidades) ───────────────────────────────
// Grafo no dirigido con pesos. adj: Map(n → Map(m → w)), simétrico;
// un self-loop guarda 2·peso interno (así k = Σ adj y m2 = Σ k).
function louvain(nodeIds, weightedEdges) {
  let g = { nodes: nodeIds.slice(), adj: new Map(nodeIds.map(id => [id, new Map()])) };
  weightedEdges.forEach(([a, b, w]) => {
    if (a === b) return;
    const ma = g.adj.get(a), mb = g.adj.get(b);
    ma.set(b, (ma.get(b) || 0) + w);
    mb.set(a, (mb.get(a) || 0) + w);
  });

  const partition = new Map(nodeIds.map(id => [id, id]));   // nodo original → super-nodo

  for (let level = 0; level < 12; level++) {
    const k = new Map();
    let m2 = 0;
    g.nodes.forEach(n => {
      let s = 0;
      g.adj.get(n).forEach(w => { s += w; });
      k.set(n, s);
      m2 += s;
    });
    if (m2 === 0) break;

    const comm = new Map(g.nodes.map(n => [n, n]));
    const tot = new Map(g.nodes.map(n => [n, k.get(n)]));
    let improved = false;

    for (let pass = 0; pass < 25; pass++) {
      let moved = false;
      for (const n of g.nodes) {
        const cn = comm.get(n), kn = k.get(n);
        const wTo = new Map();
        g.adj.get(n).forEach((w, nb) => {
          if (nb === n) return;
          const c = comm.get(nb);
          wTo.set(c, (wTo.get(c) || 0) + w);
        });
        tot.set(cn, tot.get(cn) - kn);
        let best = cn;
        let bestGain = (wTo.get(cn) || 0) - tot.get(cn) * kn / m2;
        wTo.forEach((w, c) => {
          const gain = w - tot.get(c) * kn / m2;
          if (gain > bestGain + 1e-12) { bestGain = gain; best = c; }
        });
        tot.set(best, tot.get(best) + kn);
        if (best !== cn) { comm.set(n, best); moved = true; improved = true; }
      }
      if (!moved) break;
    }
    if (!improved) break;

    partition.forEach((sup, orig) => partition.set(orig, comm.get(sup)));

    // aaa agregar: cada comunidad pasa a ser un super-nodo -bynd
    const supers = Array.from(new Set(comm.values()));
    const adj2 = new Map(supers.map(c => [c, new Map()]));
    g.nodes.forEach(u => {
      const cu = comm.get(u);
      g.adj.get(u).forEach((w, v) => {
        const cv = comm.get(v);
        const m = adj2.get(cu);
        m.set(cv, (m.get(cv) || 0) + w);
      });
    });
    g = { nodes: supers, adj: adj2 };
  }
  return partition;
}

// ─── REDES: métricas + tier ──────────────────────────────
function computeNetworks() {
  const ids = state.nodes.map(n => n.id);
  const edges = state.links.map(l => {
    const w = (l.types.has('follows') ? EDGE_WEIGHT.follows : 0) +
              (l.types.has('origen') ? EDGE_WEIGHT.origen : 0);
    return [l.source.id || l.source, l.target.id || l.target, w];
  });
  const part = louvain(ids, edges);

  const groups = new Map();
  part.forEach((c, id) => {
    if (!groups.has(c)) groups.set(c, []);
    groups.get(c).push(id);
  });

  const nets = [];
  groups.forEach(members => {
    if (members.length < MIN_NET_SIZE) return;
    // ey una familia muerta ya se ve en morado, no es "red" -bynd
    if (members.every(id => state.deadSet.has(id))) return;
    const set = new Set(members);
    let mutuals = 0, yours = 0, seen = 0, followsYou = 0, scoreSum = 0, scoreN = 0;
    members.forEach(id => {
      const n = state.nodeMap.get(id);
      if (n.mutual) mutuals++;
      if (isYours(n)) yours++;
      if (n.kind === 'seen') seen++;
      if (n.red?.follows_you) followsYou++;
      if (n.red && n.red.score != null) { scoreSum += Number(n.red.score); scoreN++; }
    });
    const size = members.length;
    const index = (0.6 * mutuals + 0.4 * yours) / size;
    const tier = (mutuals >= 2 && index >= 0.35) ? 'infiltrated'
               : (mutuals >= 1 || index >= 0.20) ? 'contact'
               : 'cold';

    // ey hubs = los mas seguidos DENTRO de la red (follows), luego grado -bynd
    const hubScore = id => {
      let fin = 0;
      state.followIn.get(id)?.forEach(x => { if (set.has(x)) fin++; });
      let deg = 0;
      state.adj.get(id)?.forEach(x => { if (set.has(x)) deg++; });
      return fin * 10 + deg;
    };
    const hubs = members.slice().sort((a, b) => hubScore(b) - hubScore(a)).slice(0, 3);

    // aaa nombre = el mas conectado dentro de la red (sigue o lo siguen) -bynd
    const centrality = id => {
      let deg = 0, fin = 0;
      state.adj.get(id)?.forEach(x => { if (set.has(x)) deg++; });
      state.followIn.get(id)?.forEach(x => { if (set.has(x)) fin++; });
      return deg + fin;
    };
    const name = members.reduce((best, id) => centrality(id) > centrality(best) ? id : best, members[0]);

    nets.push({
      members, set, size, mutuals, yours, seen, followsYou, index, tier, hubs,
      avgScore: scoreN ? scoreSum / scoreN : null,
      name,
    });
  });

  nets.sort((a, b) => b.index - a.index || b.size - a.size);
  nets.forEach((n, i) => { n.id = i; });

  const netOf = new Map();
  nets.forEach(net => net.members.forEach(id => netOf.set(id, net)));

  // aaa cuerpos para el layout: cada comunidad (incl. chicas y sueltos) es un cuerpo -bynd
  const bodies = [];
  const groupOf = new Map();
  groups.forEach((members, c) => {
    const net = netOf.get(members[0]) || null;
    const key = net ? `n${net.id}` : `p${c}`;
    bodies.push({ key, ids: members, net });
    members.forEach(id => groupOf.set(id, key));
  });
  bodies.sort((a, b) => b.ids.length - a.ids.length);
  return { nets, netOf, bodies, groupOf };
}

// ─── FUERZA DE CONSTELACIONES ────────────────────────────
function bodyRadius(n) {
  return CONST.bodyBase + CONST.bodyPerNode * Math.sqrt(n);
}

// ey roles por conexiones afuera vs adentro de su cuerpo -bynd
function computeRoles() {
  const roles = new Map();
  state.nodes.forEach(n => {
    const g = state.groupOf.get(n.id);
    let ins = 0, outs = 0;
    state.adj.get(n.id)?.forEach(m => { if (state.groupOf.get(m) === g) ins++; else outs++; });
    if (!outs) return;
    // satelite solo tiene sentido saliendo de una red (cuerpo con casco)
    const inNet = state.netOf.has(n.id);
    roles.set(n.id, inNet && outs >= ins ? 'satellite' : 'bridge');
  });
  return roles;
}

function forceConstellations() {
  let bodies = [];
  let pairs = [];          // [A, B, k] cuerpos conectados con k aristas
  let ext = [];            // [{ node, body, outs:[node], role }]
  let linked = new Set();  // idxA*100000+idxB de cuerpos conectados

  function force(alpha) {
    const sep = CONST.separation;
    // centroides solo con el nucleo (los satelites no jalan el centro)
    for (const b of bodies) {
      let x = 0, y = 0, c = 0;
      for (const n of b.core) { x += n.x; y += n.y; c++; }
      if (!c) for (const n of b.nodes) { x += n.x; y += n.y; c++; }
      b.cx = x / c;
      b.cy = y / c;
      b.vx = 0; b.vy = 0;
    }

    // cuerpo vs cuerpo: colision dura + repulsion suave a distancia
    const gap = CONST.gap * sep;
    for (let i = 0; i < bodies.length; i++) {
      const A = bodies[i];
      for (let j = i + 1; j < bodies.length; j++) {
        const B = bodies[j];
        let dx = B.cx - A.cx, dy = B.cy - A.cy;
        let d2 = dx * dx + dy * dy;
        if (d2 < 1e-6) { dx = (Math.random() - 0.5); dy = (Math.random() - 0.5); d2 = dx * dx + dy * dy; }
        const d = Math.sqrt(d2);
        const minD = A.r + B.r + gap * Math.max(0.15, Math.min(A.gapW, B.gapW));
        let push = 0;
        if (d < minD) push += (minD - d) * CONST.collide;
        const reach = minD * 3;
        // ey cuerpos conectados no se empujan a distancia, solo chocan -bynd
        if (d < reach && !linked.has(A.idx * 100000 + B.idx)) push += CONST.repulsion * sep * Math.sqrt(A.mass * B.mass) / (d + 30) * (1 - d / reach) * 0.05;
        if (!push) continue;
        const ux = dx / d, uy = dy / d;
        const tot = A.mass + B.mass;
        const fa = push * (B.mass / tot) * alpha, fb = push * (A.mass / tot) * alpha;
        A.vx -= ux * fa; A.vy -= uy * fa;
        B.vx += ux * fb; B.vy += uy * fb;
      }
    }

    // aaa resortes entre cuerpos conectados: quedan vecinos, no al otro lado del mapa -bynd
    for (const [A, B, k] of pairs) {
      const dx = B.cx - A.cx, dy = B.cy - A.cy;
      const d = Math.sqrt(dx * dx + dy * dy) || 1;
      const target = A.r + B.r + gap * Math.max(0.15, Math.min(A.gapW, B.gapW)) * 1.15;
      if (d <= target) continue;
      const pull = (d - target) * CONST.bodySpring * Math.min(1.5, Math.log1p(k) / 1.5) * alpha;
      const ux = dx / d, uy = dy / d;
      const tot = A.mass + B.mass;
      A.vx += ux * pull * (B.mass / tot); A.vy += uy * pull * (B.mass / tot);
      B.vx -= ux * pull * (A.mass / tot); B.vy -= uy * pull * (A.mass / tot);
    }

    // aplicar: traslacion del cuerpo + cohesion de cada nodo del nucleo
    const k = CONST.cohesion * alpha;
    for (const b of bodies) {
      for (const n of b.nodes) {
        n.vx += b.vx;
        n.vy += b.vy;
        if (!n.__sat) {
          n.vx += (b.cx - n.x) * k;
          n.vy += (b.cy - n.y) * k;
        }
      }
    }

    // puentes a la orilla · satelites afuera, del lado de sus vecinos externos
    for (const e of ext) {
      let mx = 0, my = 0;
      for (const o of e.outs) { mx += o.x; my += o.y; }
      mx /= e.outs.length; my /= e.outs.length;
      const b = e.body;
      let dx = mx - b.cx, dy = my - b.cy;
      const d = Math.sqrt(dx * dx + dy * dy) || 1;
      dx /= d; dy /= d;
      if (e.role === 'satellite') {
        const out = Math.min(d * 0.6, b.r + gap * CONST.satOut);
        const tx = b.cx + dx * out, ty = b.cy + dy * out;
        e.node.vx += (tx - e.node.x) * CONST.satPull * alpha;
        e.node.vy += (ty - e.node.y) * CONST.satPull * alpha;
      } else {
        const tx = b.cx + dx * b.r * 0.85, ty = b.cy + dy * b.r * 0.85;
        const w = CONST.rimPull * e.share * alpha;
        e.node.vx += (tx - e.node.x) * w;
        e.node.vy += (ty - e.node.y) * w;
      }
    }
  }

  force.initialize = (nodes) => {
    const byKey = new Map();
    const bodyOf = new Map();
    nodes.forEach(n => {
      const key = state.groupOf.get(n.id) || `s:${n.id}`;
      if (!byKey.has(key)) byKey.set(key, []);
      byKey.get(key).push(n);
      n.__sat = state.roles.get(n.id) === 'satellite';
    });
    bodies = Array.from(byKey.values()).map(ns => {
      const b = {
        nodes: ns,
        core: ns.filter(n => !n.__sat),
        mass: ns.length,
        r: bodyRadius(ns.length),
        cx: 0, cy: 0, vx: 0, vy: 0,
        // ey cuerpos sueltos (sin red) piden poco espacio: no abren huecos entre constelaciones -bynd
        gapW: Math.min(1, Math.sqrt(ns.length) / 4),
      };
      ns.forEach(n => bodyOf.set(n.id, b));
      return b;
    });
    bodies.forEach((b, i) => { b.idx = i; });

    // pares de cuerpos conectados
    const pk = new Map();
    state.links.forEach(l => {
      const A = bodyOf.get(l.source.id || l.source), B = bodyOf.get(l.target.id || l.target);
      if (!A || !B || A === B) return;
      const [x, y] = bodies.indexOf(A) < bodies.indexOf(B) ? [A, B] : [B, A];
      const key = bodies.indexOf(x) + '|' + bodies.indexOf(y);
      if (!pk.has(key)) pk.set(key, [x, y, 0]);
      pk.get(key)[2]++;
    });
    pairs = Array.from(pk.values());
    linked = new Set(pairs.map(([x, y]) => Math.min(x.idx, y.idx) * 100000 + Math.max(x.idx, y.idx)));

    // nodos con vecinos afuera
    ext = [];
    nodes.forEach(n => {
      const role = state.roles.get(n.id);
      if (!role) return;
      const b = bodyOf.get(n.id);
      const outs = [];
      let ins = 0;
      state.adj.get(n.id)?.forEach(m => {
        const o = state.nodeMap.get(m);
        if (bodyOf.get(m) === b) ins++; else if (o) outs.push(o);
      });
      if (outs.length) ext.push({ node: n, body: b, outs, role, share: outs.length / (outs.length + ins) });
    });
  };

  return force;
}

// q chidoteee posicion inicial: pre-acomodo de los CUERPOS segun sus conexiones -bynd
// (sin esto, dos constelaciones conectadas pueden nacer en lados opuestos y ya no
//  pueden cruzarse entre las demas para juntarse)
function seedPositions(width, height) {
  const sep = CONST.separation;
  const idx = new Map();
  const bnodes = state.bodies.map((b, i) => {
    b.ids.forEach(id => idx.set(id, i));
    const r = bodyRadius(b.ids.length);
    return { i, r, n: b.ids.length, net: !!b.net, gapW: Math.min(1, Math.sqrt(b.ids.length) / 4) };
  });
  const pk = new Map();
  state.links.forEach(l => {
    const a = idx.get(l.source.id || l.source), c = idx.get(l.target.id || l.target);
    if (a == null || c == null || a === c) return;
    const key = Math.min(a, c) + '|' + Math.max(a, c);
    if (!pk.has(key)) pk.set(key, { source: Math.min(a, c), target: Math.max(a, c), k: 0 });
    pk.get(key).k++;
  });
  const blinks = Array.from(pk.values());
  const gapOf = (A, B) => CONST.gap * sep * Math.max(0.15, Math.min(A.gapW, B.gapW));

  // espiral como punto de partida (grandes al centro)
  const golden = Math.PI * (3 - Math.sqrt(5));
  let acc = 0;
  bnodes.forEach((b, i) => {
    acc += b.r + CONST.gap * sep * 0.6;
    const dist = i === 0 ? 0 : Math.sqrt(acc) * 14;
    b.x = width / 2 + Math.cos(i * golden) * dist;
    b.y = height / 2 + Math.sin(i * golden) * dist;
  });

  const pre = d3.forceSimulation(bnodes)
    .force('link', d3.forceLink(blinks).id(d => d.i)
      .distance(l => l.source.r + l.target.r + gapOf(l.source, l.target) * 1.15)
      .strength(l => Math.min(1, 0.25 + Math.log1p(l.k) / 3)))
    .force('charge', d3.forceManyBody().strength(b => -30 * Math.sqrt(b.n) * sep))
    .force('collide', d3.forceCollide().radius(b => b.r + CONST.gap * sep * b.gapW * 0.5).iterations(3))
    .force('x', d3.forceX(width / 2).strength(b => b.net ? 0.06 : 0.02))
    .force('y', d3.forceY(height / 2).strength(b => b.net ? 0.06 : 0.02))
    .stop();
  for (let t = 0; t < 400; t++) pre.tick();

  state.bodies.forEach((b, i) => {
    const c = bnodes[i];
    b.ids.forEach(id => {
      const n = state.nodeMap.get(id);
      if (!n || n.x != null) return;
      const rr = c.r * Math.sqrt(Math.random()) * 0.8, aa = Math.random() * 2 * Math.PI;
      n.x = c.x + Math.cos(aa) * rr;
      n.y = c.y + Math.sin(aa) * rr;
    });
  });
}

function sameBody(l) {
  const s = l.source.id || l.source, t = l.target.id || l.target;
  return state.groupOf.get(s) === state.groupOf.get(t);
}

// ─── BFS SHORTEST PATH ───────────────────────────────────
function shortestPath(adj, fromId, toId) {
  if (!adj.has(fromId) || !adj.has(toId)) return null;
  if (fromId === toId) return [fromId];
  const prev = new Map([[fromId, null]]);
  const queue = [fromId];
  while (queue.length) {
    const cur = queue.shift();
    if (cur === toId) {
      const path = [];
      for (let x = cur; x !== null; x = prev.get(x)) path.unshift(x);
      return path;
    }
    adj.get(cur)?.forEach(nb => {
      if (!prev.has(nb)) { prev.set(nb, cur); queue.push(nb); }
    });
  }
  return null;
}

// ─── D3 RENDERING ────────────────────────────────────────
let svg, gZoom, gHulls, gLinks, gNodes, simulation, zoomBehavior;
let allLinksSel, allNodesSel;
const hullLine = d3.line().curve(d3.curveCatmullRomClosed.alpha(0.6));

function initSvg() {
  svg = d3.select('#graph');
  svg.selectAll('*').remove();

  const defs = svg.append('defs');
  const mk = (id, color) => defs.append('marker')
    .attr('id', id)
    .attr('viewBox', '0 -5 10 10')
    .attr('refX', 16).attr('refY', 0)
    .attr('markerWidth', 6).attr('markerHeight', 6)
    .attr('orient', 'auto')
    .append('path').attr('d', 'M0,-5L10,0L0,5').attr('fill', color);
  mk('arrow', '#555');
  mk('arrow-origen', '#333');
  mk('arrow-hl', '#E8FF00');
  mk('arrow-path', '#FF00B3');
  mk('arrow-dead', DEAD_COLOR);

  gZoom = svg.append('g').attr('class', 'zoom-layer');
  gHulls = gZoom.append('g').attr('class', 'hulls');
  gLinks = gZoom.append('g').attr('class', 'links');
  gNodes = gZoom.append('g').attr('class', 'nodes');

  zoomBehavior = d3.zoom()
    .scaleExtent([0.08, 8])
    .on('zoom', (e) => gZoom.attr('transform', e.transform));
  svg.call(zoomBehavior);
}

function destroySimulation() {
  if (simulation) { simulation.stop(); simulation = null; }
  if (svg) svg.selectAll('*').remove();
}

function tierColorOf(d) {
  const net = state.netOf.get(d.id);
  return net ? TIER[net.tier].color : '#2a2a2a';
}

function nodeColor(d) {
  const dead = state.deadSet.has(d.id);
  if (state.colorMode === 'network') {
    if (d.ghost || d.kind === 'seen') return 'transparent';
    return tierColorOf(d);
  }
  if (dead) return d.ghost ? 'transparent' : DEAD_COLOR;
  if (d.ghost) return 'transparent';
  if (d.mutual) return '#E8FF00';
  if (d.kind === 'seen' || d.kind === 'external') return '#0a0a0a';
  if (DEAD_STATUSES.has(d.status)) return '#444';
  return '#f5f5f5';
}
function nodeStroke(d) {
  if (state.colorMode === 'network') {
    return d.ghost ? '#666' : tierColorOf(d);
  }
  if (state.deadSet.has(d.id)) return DEAD_COLOR;
  if (d.ghost) return '#666';
  if (d.mutual) return '#E8FF00';
  if (d.kind === 'seen') return '#FF00B3';
  if (d.kind === 'external') return '#f5f5f5';
  if (DEAD_STATUSES.has(d.status)) return '#444';
  return '#f5f5f5';
}
function nodeRadius(d) {
  const deg = state.adj.get(d.id)?.size || 1;
  const fin = state.followIn.get(d.id)?.size || 0;
  // q chidoteee los q muchos de tu red siguen se ven mas grandes -bynd
  return Math.min(16, 4 + Math.sqrt(deg) * 1.3 + Math.sqrt(fin) * 1.2);
}

function linkIsDead(d) {
  const s = d.source.id || d.source;
  const t = d.target.id || d.target;
  return d.kind === 'origen' && state.deadSet.has(s) && state.deadSet.has(t);
}

function linkVisible(d) {
  if (d.types.has('follows') && state.showFollows) return true;
  if (d.types.has('origen') && state.showOrigen) return true;
  return false;
}

function render() {
  const { width, height } = svg.node().getBoundingClientRect();

  const linkSel = gLinks.selectAll('line.link')
    .data(state.links, d => `${(d.source.id || d.source)}|${(d.target.id || d.target)}`);
  linkSel.exit().remove();
  allLinksSel = linkSel.enter().append('line').merge(linkSel)
    .attr('class', d => `link ${d.kind}`);

  const nodeSel = gNodes.selectAll('g.node').data(state.nodes, d => d.id);
  nodeSel.exit().remove();
  const nodeEnter = nodeSel.enter().append('g').attr('class', 'node');
  nodeEnter.append('circle');
  nodeEnter.append('text');
  allNodesSel = nodeEnter.merge(nodeSel);

  allNodesSel
    .on('click', (e, d) => { e.stopPropagation(); selectNode(d.id); })
    .on('mouseenter', (e, d) => showTooltip(e, d))
    .on('mousemove', moveTooltip)
    .on('mouseleave', hideTooltip)
    .call(d3.drag()
      .on('start', (e, d) => { if (!e.active) simulation.alphaTarget(0.3).restart(); d.fx = d.x; d.fy = d.y; })
      .on('drag', (e, d) => { d.fx = e.x; d.fy = e.y; })
      .on('end', (e, d) => { if (!e.active) simulation.alphaTarget(0); if (!state.frozen) { d.fx = null; d.fy = null; } }));

  styleGraph();

  if (simulation) simulation.stop();
  seedPositions(width, height);
  simulation = d3.forceSimulation(state.nodes)
    .force('link', d3.forceLink(state.links).id(d => d.id)
      // ey adentro del cuerpo: aristas cortas y firmes; puentes entre cuerpos: largos y flojos -bynd
      .distance(d => sameBody(d) ? (d.kind === 'follows' ? 45 : 60) : CONST.bridgeDist * CONST.separation)
      .strength(d => sameBody(d) ? (d.kind === 'follows' ? 0.5 : 0.3) : CONST.bridgeStrength))
    // aaa la carga solo separa vecinos; el acomodo global lo hacen las constelaciones -bynd
    .force('charge', d3.forceManyBody().strength(-90).distanceMax(160))
    .force('constellations', forceConstellations())
    // aaa las redes gravitan al centro; los sueltos casi no, asi quedan de halo afuera -bynd
    .force('x', d3.forceX(width / 2).strength(d => state.netOf.has(d.id) ? 0.02 : 0.008))
    .force('y', d3.forceY(height / 2).strength(d => state.netOf.has(d.id) ? 0.02 : 0.008))
    .force('collide', d3.forceCollide().radius(d => nodeRadius(d) + 5).iterations(2))
    .alpha(1)
    .alphaDecay(0.02);

  let tick = 0;
  simulation.on('tick', () => {
    allLinksSel
      .attr('x1', d => d.source.x).attr('y1', d => d.source.y)
      .attr('x2', d => d.target.x).attr('y2', d => d.target.y);
    allNodesSel.attr('transform', d => `translate(${d.x},${d.y})`);
    if (tick++ % 3 === 0) drawHulls();
  });
  simulation.on('end', drawHulls);

  svg.on('click', () => { selectNode(null); });
}

// ey estilos q dependen de modo de color / toggles (sin reiniciar simulacion) -bynd
function styleGraph() {
  allNodesSel.select('circle')
    .attr('r', nodeRadius)
    .attr('fill', nodeColor)
    .attr('stroke', nodeStroke)
    .attr('stroke-width', 1.5)
    .attr('stroke-dasharray', d => d.ghost ? '2,2' : null);
  allNodesSel.select('text')
    .attr('dy', d => nodeRadius(d) + 10)
    .text(d => d.id)
    .style('display', state.showLabels ? null : 'none');
  allLinksSel
    .style('display', d => linkVisible(d) ? null : 'none')
    .style('stroke', d => linkIsDead(d) ? DEAD_COLOR : null)
    .style('stroke-opacity', d => linkIsDead(d) ? 0.5 : null);
}

// ─── HULLS DE REDES ──────────────────────────────────────
function hullPoints(net) {
  const pts = [];
  net.members.forEach(id => {
    const n = state.nodeMap.get(id);
    if (n.x == null) return;
    if (state.roles.get(id) === 'satellite') return;   // ey el satelite tiene su propio globito -bynd
    const r = nodeRadius(n) + 14;
    pts.push([n.x - r, n.y], [n.x + r, n.y], [n.x, n.y - r], [n.x, n.y + r]);
  });
  return pts.length >= 6 ? d3.polygonHull(pts) : null;
}

function drawHulls() {
  if (!gHulls) return;
  const nets = state.showHulls ? state.nets : [];

  const sel = gHulls.selectAll('g.hull').data(nets, d => d.id);
  sel.exit().remove();
  const enter = sel.enter().append('g').attr('class', 'hull');
  enter.append('path');
  enter.append('text');
  const all = enter.merge(sel);

  all.attr('class', d => `hull tier-${d.tier}` +
    (state.focusNet != null && state.focusNet !== d.id ? ' dim' : '') +
    (state.focusNet === d.id ? ' focus' : ''));

  all.each(function (net) {
    const g = d3.select(this);
    const hull = hullPoints(net);
    if (!hull) { g.style('display', 'none'); return; }
    g.style('display', null);
    const c = TIER[net.tier].color;
    g.select('path')
      .attr('d', hullLine(hull))
      .attr('fill', c)
      .attr('fill-opacity', 0.03 + net.index * 0.12)
      .attr('stroke', c)
      .attr('stroke-opacity', net.tier === 'cold' ? 0.35 : 0.6)
      .attr('stroke-dasharray', net.tier === 'cold' ? '4,4' : null)
      .on('click', (e) => { e.stopPropagation(); toggleFocusNet(net.id); });

    // aaa etiqueta arriba del casco -bynd
    let top = hull[0];
    hull.forEach(p => { if (p[1] < top[1]) top = p; });
    const cx = d3.mean(hull, p => p[0]);
    g.select('text')
      .attr('x', cx).attr('y', top[1] - 6)
      .attr('fill', c)
      .text(`${TIER[net.tier].label} · @${net.name} · ${Math.round(net.index * 100)}%`);
  });

  // aaa globitos de satelites: mismo color que su red, punteados -bynd
  const sats = state.showHulls
    ? state.nodes.filter(n => state.roles.get(n.id) === 'satellite' && state.netOf.has(n.id) && n.x != null)
    : [];
  const ss = gHulls.selectAll('circle.sat-bubble').data(sats, d => d.id);
  ss.exit().remove();
  ss.enter().append('circle').attr('class', 'sat-bubble')
    .merge(ss)
    .attr('cx', d => d.x).attr('cy', d => d.y)
    .attr('r', d => nodeRadius(d) + 12)
    .attr('fill', d => TIER[state.netOf.get(d.id).tier].color)
    .attr('fill-opacity', 0.08)
    .attr('stroke', d => TIER[state.netOf.get(d.id).tier].color)
    .attr('stroke-opacity', 0.7)
    .attr('stroke-dasharray', '3,3')
    .style('opacity', d => state.focusNet != null && state.netOf.get(d.id).id !== state.focusNet ? 0.12 : null)
    .style('pointer-events', 'none');
}

// ─── HIGHLIGHTS ──────────────────────────────────────────
function matchesFilter(d) {
  switch (state.filter) {
    case 'mutual': return d.mutual;
    case 'active': return d.status === 'active';
    case 'unfollowed': return DEAD_STATUSES.has(d.status);
    case 'origin': return d.ghost || (state.outAdj.get(d.id)?.size > 0);
    case 'seen': return d.kind === 'seen';
    case 'infiltrated': return state.netOf.get(d.id)?.tier === 'infiltrated';
    case 'dead': return state.deadSet.has(d.id);
    default: return true;
  }
}

function applyHighlights() {
  if (!allNodesSel) return;
  const sel = state.selectedId;
  const path = state.pathIds;
  const search = (document.getElementById('searchInput').value || '').toLowerCase().trim();
  const focus = state.focusNet != null ? state.nets[state.focusNet] : null;
  const neighbors = sel ? (state.adj.get(sel) || new Set()) : null;

  const dimMap = new Map();
  allNodesSel.each(function (d) {
    const el = d3.select(this);
    let dim = !matchesFilter(d);
    let highlight = false;
    if (search && !d.id.toLowerCase().includes(search)) dim = true;
    if (focus && !focus.set.has(d.id)) dim = true;

    if (sel) {
      if (d.id === sel || neighbors.has(d.id)) { dim = false; highlight = (d.id !== sel); }
      else dim = true;
    }
    const inPath = path.has(d.id);
    if (inPath) dim = false;

    dimMap.set(d.id, dim);
    el.classed('dim', dim);
    el.classed('highlight', highlight && !inPath);
    el.classed('selected', d.id === sel && !inPath);
    el.classed('path', inPath);
  });

  const ordered = state.pathOrdered || [];
  const pathPairs = new Set();
  for (let i = 0; i < ordered.length - 1; i++) {
    pathPairs.add(`${ordered[i]}|${ordered[i + 1]}`);
    pathPairs.add(`${ordered[i + 1]}|${ordered[i]}`);
  }

  allLinksSel.each(function (d) {
    const el = d3.select(this);
    const sId = d.source.id || d.source;
    const tId = d.target.id || d.target;
    const inPath = pathPairs.has(`${sId}|${tId}`);
    let dim = dimMap.get(sId) || dimMap.get(tId);
    let highlight = false;
    if (sel) {
      if (sId === sel || tId === sel) { highlight = true; dim = false; }
      else dim = true;
    }
    if (inPath) { dim = false; highlight = false; }

    el.classed('dim', dim);
    el.classed('highlight', highlight);
    el.classed('path', inPath);

    let marker = d.kind === 'origen' ? 'url(#arrow-origen)' : 'url(#arrow)';
    if (inPath) marker = 'url(#arrow-path)';
    else if (highlight) marker = 'url(#arrow-hl)';
    else if (linkIsDead(d)) marker = 'url(#arrow-dead)';
    el.attr('marker-end', marker);
  });

  drawHulls();
}

// ─── TOOLTIP ─────────────────────────────────────────────
const tooltipEl = document.getElementById('tooltip');
const KIND_LABEL = {
  tracked: null,
  seen: 'perfil visto · no lo sigues',
  external: 'lo sigues (fuera del bot)',
  origin: '[ origin only ]',
};
function showTooltip(e, d) {
  const fin = state.followIn.get(d.id)?.size || 0;
  const fout = state.followOut.get(d.id)?.size || 0;
  const deadTag = state.deadSet.has(d.id) ? ' · dead family' : '';
  const net = state.netOf.get(d.id);
  const kind = KIND_LABEL[d.kind] || (d.status || '—');
  tooltipEl.innerHTML = `
    <div class="tooltip-name">@${d.id}</div>
    <div>${kind}${d.mutual ? ' · mutual' : ''}${deadTag}</div>
    <div style="color:var(--muted);margin-top:2px;">lo siguen ${fin} · sigue ${fout}</div>
    ${net ? `<div style="color:${TIER[net.tier].color};margin-top:2px;">red @${net.name} · ${TIER[net.tier].label}</div>` : ''}
    ${d.red ? `<div style="color:var(--muted);">score ${d.red.score}</div>` : ''}
  `;
  tooltipEl.classList.add('show');
  moveTooltip(e);
}
function moveTooltip(e) {
  tooltipEl.style.left = (e.pageX + 14) + 'px';
  tooltipEl.style.top = (e.pageY + 14) + 'px';
}
function hideTooltip() { tooltipEl.classList.remove('show'); }

// ─── SELECT NODE ─────────────────────────────────────────
function selectNode(id) {
  state.selectedId = id;
  renderNodeInfo();
  applyHighlights();
}

function chipList(title, ids, cls) {
  if (!ids.length) return '';
  let html = `<div class="neighbors-title">${title}</div>`;
  ids.slice(0, 30).forEach(n => html += `<span class="neighbor-chip ${cls}" data-jump="${n}">@${n}</span>`);
  if (ids.length > 30) html += `<span class="neighbor-chip">+${ids.length - 30}</span>`;
  return html;
}

function renderNodeInfo() {
  const box = document.getElementById('nodeInfo');
  if (!state.selectedId) {
    box.innerHTML = '<div class="node-info-empty">click any node in the graph</div>';
    return;
  }
  const d = state.nodeMap.get(state.selectedId);
  if (!d) { box.innerHTML = '<div class="node-info-empty">node not found</div>'; return; }

  const ins = Array.from(state.inAdj.get(d.id) || []);
  const outs = Array.from(state.outAdj.get(d.id) || []);
  const fins = Array.from(state.followIn.get(d.id) || []);
  const fouts = Array.from(state.followOut.get(d.id) || []);
  const net = state.netOf.get(d.id);

  let html = `<div class="node-info-name">${d.id}</div><dl>`;
  if (state.deadSet.has(d.id)) html += `<dt>family</dt><dd style="color:${DEAD_COLOR};">dead branch</dd>`;
  const role = state.roles.get(d.id);
  if (role === 'satellite') html += `<dt>posición</dt><dd class="pink">satélite · más conexiones afuera que adentro</dd>`;
  else if (role === 'bridge') html += `<dt>posición</dt><dd>puente · conecta con otra constelación</dd>`;
  if (net) {
    html += `<dt>red</dt><dd><span class="tier-badge tier-${net.tier}" data-net="${net.id}">${TIER[net.tier].label}</span> @${net.name}</dd>`;
    if (net.hubs.includes(d.id)) html += `<dt>rol</dt><dd class="accent">hub de su red</dd>`;
  }

  if (d.kind === 'tracked') {
    html += `<dt>status</dt><dd class="${d.status === 'active' ? 'accent' : ''}">${d.status || '—'}</dd>`;
    html += `<dt>mutual</dt><dd class="${d.mutual ? 'accent' : ''}">${d.mutual ? 'yes' : 'no'}</dd>`;
    html += `<dt>origen</dt><dd class="pink">${d.origen || '—'}</dd>`;
    if (d.request_state) html += `<dt>request</dt><dd>${d.request_state}</dd>`;
    if (d.is_private != null) html += `<dt>cuenta</dt><dd>${d.is_private ? 'privada' : 'pública'}</dd>`;
    if (d.followed_at) html += `<dt>followed</dt><dd>${d.followed_at.slice(0, 10)}</dd>`;
    if (d.unfollowed_at) html += `<dt>unfollowed</dt><dd class="pink">${d.unfollowed_at.slice(0, 10)}</dd>`;
    if (d.last_updated) html += `<dt>updated</dt><dd>${d.last_updated.slice(0, 10)}</dd>`;
    if (d.profile_followers !== '') html += `<dt>followers</dt><dd>${d.profile_followers}</dd>`;
    if (d.profile_following !== '') html += `<dt>following</dt><dd>${d.profile_following}</dd>`;
    if (d.profile_ratio !== '') html += `<dt>ratio</dt><dd>${d.profile_ratio}</dd>`;
    if (d.stand_type) html += `<dt>type</dt><dd>${d.stand_type}</dd>`;
  } else {
    html += `<dt>type</dt><dd class="accent">${KIND_LABEL[d.kind]}</dd>`;
  }

  if (d.red) {
    html += `<dt>score red</dt><dd class="accent">${d.red.score}</dd>`;
    html += `<dt>conexiones</dt><dd>${d.red.total_conns} (${d.red.mutual_conns} mutual)</dd>`;
    if (d.red.follows_you) html += `<dt>te sigue</dt><dd class="accent">yes</dd>`;
    if (d.red.checked_at) html += `<dt>evaluado</dt><dd>${String(d.red.checked_at).slice(0, 10)}</dd>`;
  }
  html += `<dt>lo siguen</dt><dd>${fins.length}</dd>`;
  html += `<dt>sigue a</dt><dd>${fouts.length}</dd>`;
  html += '</dl>';

  if (ins.length || outs.length || fins.length || fouts.length) {
    html += '<div class="neighbors">';
    html += chipList('← lo siguen (gente que sigues)', fins, 'in');
    html += chipList('→ sigue a', fouts, 'out');
    html += chipList('← origen (cacheado desde)', ins, 'in');
    html += chipList('→ spawned (cacheados desde aquí)', outs, 'out');
    html += '</div>';
  }

  box.innerHTML = html;
  box.querySelectorAll('[data-jump]').forEach(el => {
    el.addEventListener('click', () => { const id = el.getAttribute('data-jump'); selectNode(id); focusNode(id); });
  });
  box.querySelectorAll('[data-net]').forEach(el => {
    el.addEventListener('click', () => toggleFocusNet(Number(el.getAttribute('data-net'))));
  });
}

// ─── SEARCH ──────────────────────────────────────────────
function runSearch() {
  const q = document.getElementById('searchInput').value.toLowerCase().trim();
  const box = document.getElementById('searchResults');
  if (!q) { box.innerHTML = ''; applyHighlights(); return; }

  const matches = state.nodes
    .filter(n => n.id.toLowerCase().includes(q) && matchesFilter(n))
    .slice(0, 50);

  box.innerHTML = matches.map(n => {
    const tag = state.deadSet.has(n.id) ? 'dead'
      : n.ghost ? 'origin'
      : n.mutual ? 'mutual'
      : n.kind === 'tracked' ? (n.status || '—') : n.kind;
    return `<div class="search-result" data-id="${n.id}">
      <span>@${n.id}</span><span class="badge">${tag}</span>
    </div>`;
  }).join('');
  box.querySelectorAll('.search-result').forEach(el => {
    el.addEventListener('click', () => {
      const id = el.getAttribute('data-id');
      selectNode(id);
      focusNode(id);
    });
  });
  applyHighlights();
}

function focusNode(id) {
  const n = state.nodeMap.get(id);
  if (!n || n.x == null) return;
  const { width, height } = svg.node().getBoundingClientRect();
  const k = 1.6;
  const t = d3.zoomIdentity.translate(width / 2 - n.x * k, height / 2 - n.y * k).scale(k);
  svg.transition().duration(500).call(zoomBehavior.transform, t);
}

function zoomToMembers(ids) {
  const pts = ids.map(id => state.nodeMap.get(id)).filter(n => n && n.x != null);
  if (!pts.length) return;
  const { width, height } = svg.node().getBoundingClientRect();
  const [x0, x1] = d3.extent(pts, p => p.x);
  const [y0, y1] = d3.extent(pts, p => p.y);
  const pad = 80;
  const k = Math.min(3, 0.9 / Math.max((x1 - x0 + pad) / width, (y1 - y0 + pad) / height));
  const t = d3.zoomIdentity.translate(width / 2 - k * (x0 + x1) / 2, height / 2 - k * (y0 + y1) / 2).scale(k);
  svg.transition().duration(600).call(zoomBehavior.transform, t);
}

// ─── REDES: panel + foco ─────────────────────────────────
function toggleFocusNet(id) {
  state.focusNet = state.focusNet === id ? null : id;
  if (state.focusNet != null) zoomToMembers(state.nets[id].members);
  renderNetworks();
  applyHighlights();
}

function renderNetworks() {
  const list = document.getElementById('netList');
  const summary = document.getElementById('netSummary');
  if (!list) return;

  const count = t => state.nets.filter(n => n.tier === t).length;
  summary.innerHTML = state.nets.length
    ? `<span class="tier-text tier-infiltrated">${count('infiltrated')} infiltrated</span> ·
       <span class="tier-text tier-contact">${count('contact')} contact</span> ·
       <span class="tier-text tier-cold">${count('cold')} cold</span>`
    : '';

  if (!state.nets.length) {
    list.innerHTML = `<div class="path-empty">${state.hasFollowData
      ? 'no hay redes de ≥ 3 nodos todavía'
      : 'sin datos de followed_by · solo hay linaje de origen'}</div>`;
    return;
  }

  list.innerHTML = state.nets.map(net => {
    const pct = Math.round(net.index * 100);
    const hubs = net.hubs.map(h => `<span class="neighbor-chip" data-jump="${h}">@${h}</span>`).join('');
    return `<div class="net-item tier-${net.tier}${state.focusNet === net.id ? ' focus' : ''}" data-net="${net.id}">
      <div class="net-head">
        <span class="net-name">@${net.name}</span>
        <span class="tier-badge tier-${net.tier}">${TIER[net.tier].label}</span>
      </div>
      <div class="net-meta">${net.size} nodos · ${net.mutuals} mutual · ${net.yours} sigues · ${net.seen} vistos${net.followsYou ? ` · ${net.followsYou} te siguen` : ''}${net.avgScore != null ? ` · score ⌀${net.avgScore.toFixed(1)}` : ''}</div>
      <div class="net-bar"><div class="net-bar-fill" style="width:${pct}%"></div><span>${pct}%</span></div>
      <div class="net-hubs">${hubs}</div>
    </div>`;
  }).join('');

  list.querySelectorAll('.net-item').forEach(el => {
    el.addEventListener('click', () => toggleFocusNet(Number(el.getAttribute('data-net'))));
  });
  list.querySelectorAll('[data-jump]').forEach(el => {
    el.addEventListener('click', (e) => {
      e.stopPropagation();
      const id = el.getAttribute('data-jump');
      selectNode(id);
      focusNode(id);
    });
  });
}

// ─── PATH FINDING ────────────────────────────────────────
function relationLabel(a, b) {
  const parts = [];
  linkBetween(a, b).forEach(l => {
    const s = l.source.id || l.source;
    const fwd = s === a;
    if (l.types.has('follows')) parts.push(fwd ? '↓ sigue a' : '↑ lo sigue');
    if (l.types.has('origen')) parts.push(fwd ? '↓ spawned' : '↑ origen of');
  });
  return parts.join(' · ') || '·';
}

function tracePath() {
  const fromId = document.getElementById('pathFrom').value.trim().replace(/^@/, '');
  const toId = document.getElementById('pathTo').value.trim().replace(/^@/, '');
  const out = document.getElementById('pathResult');

  if (!fromId || !toId) {
    out.innerHTML = '<div class="path-empty">enter two usernames to find connection</div>';
    return;
  }
  if (!state.nodeMap.has(fromId)) { out.innerHTML = `<div class="path-fail">@${fromId} not in graph</div>`; return; }
  if (!state.nodeMap.has(toId)) { out.innerHTML = `<div class="path-fail">@${toId} not in graph</div>`; return; }

  const path = shortestPath(state.adj, fromId, toId);
  if (!path) {
    out.innerHTML = `<div class="path-fail">no path · disconnected</div>`;
    state.pathIds = new Set();
    state.pathOrdered = [];
    applyHighlights();
    return;
  }

  state.pathIds = new Set(path);
  state.pathOrdered = path;

  const hops = path.length - 1;
  let html = `<div class="path-success">${hops} hop${hops !== 1 ? 's' : ''} · ${path.length} nodes</div>`;
  path.forEach((id, i) => {
    html += `<div class="path-step" data-id="${id}">
      <span class="num">${String(i + 1).padStart(2, '0')}</span><span>@${id}</span>
    </div>`;
    if (i < path.length - 1) html += `<div class="path-arrow">${relationLabel(path[i], path[i + 1])}</div>`;
  });
  out.innerHTML = html;
  out.querySelectorAll('.path-step').forEach(el => {
    el.addEventListener('click', () => {
      const id = el.getAttribute('data-id');
      selectNode(id);
      focusNode(id);
    });
  });
  applyHighlights();
}

function clearPath() {
  document.getElementById('pathFrom').value = '';
  document.getElementById('pathTo').value = '';
  state.pathIds = new Set();
  state.pathOrdered = [];
  document.getElementById('pathResult').innerHTML = '<div class="path-empty">enter two usernames to find connection</div>';
  applyHighlights();
}

// ─── STATS RENDERING ─────────────────────────────────────
function renderStats() {
  const set = (id, v) => { const el = document.getElementById(id); if (el) el.textContent = v; };
  const nFollows = state.links.filter(l => l.types.has('follows')).length;
  const nOrigen = state.links.filter(l => l.types.has('origen')).length;
  set('statNodes', state.nodes.length);
  set('statEdges', state.links.length);
  set('statEdgesSub', `${nFollows} follows · ${nOrigen} origen`);
  set('statMutuals', state.nodes.filter(n => n.mutual).length);
  let originCount = 0;
  state.outAdj.forEach(s => { if (s.size > 0) originCount++; });
  set('statOrigins', originCount);
  set('statComponents', connectedComponents(state.nodes, state.adj));
  set('statDegree', state.nodes.length ? (2 * state.links.length / state.nodes.length).toFixed(2) : 0);
  set('statNets', state.nets.length);
  set('statInfiltrated', state.nets.filter(n => n.tier === 'infiltrated').length);
  set('statDead', state.deadSet.size);
}

// ─── DASHBOARD UI WIRING ─────────────────────────────────
function wireDashboardUI() {
  const searchInput = document.getElementById('searchInput');
  searchInput.oninput = runSearch;

  document.querySelectorAll('.chip').forEach(c => {
    c.onclick = () => {
      document.querySelectorAll('.chip').forEach(x => x.classList.remove('active'));
      c.classList.add('active');
      state.filter = c.getAttribute('data-filter');
      runSearch();
      applyHighlights();
    };
    c.classList.toggle('active', c.getAttribute('data-filter') === state.filter);
  });

  const pathFrom = document.getElementById('pathFrom');
  const pathTo = document.getElementById('pathTo');
  document.getElementById('pathBtn').onclick = tracePath;
  document.getElementById('pathClearBtn').onclick = clearPath;
  pathFrom.onkeydown = (e) => { if (e.key === 'Enter') tracePath(); };
  pathTo.onkeydown = (e) => { if (e.key === 'Enter') tracePath(); };

  document.getElementById('resetBtn').onclick = () => {
    state.focusNet = null;
    renderNetworks();
    applyHighlights();
    svg.transition().duration(400).call(zoomBehavior.transform, d3.zoomIdentity);
    if (simulation) simulation.alpha(0.6).restart();
  };
  document.getElementById('freezeBtn').onclick = (e) => {
    state.frozen = !state.frozen;
    e.currentTarget.classList.toggle('active', state.frozen);
    if (state.frozen) {
      state.nodes.forEach(n => { n.fx = n.x; n.fy = n.y; });
      simulation?.stop();
    } else {
      state.nodes.forEach(n => { n.fx = null; n.fy = null; });
      simulation?.alpha(0.3).restart();
    }
  };

  const toggle = (btnId, key, after) => {
    const b = document.getElementById(btnId);
    if (!b) return;
    b.classList.toggle('active', !!state[key]);
    b.onclick = () => {
      state[key] = !state[key];
      b.classList.toggle('active', state[key]);
      after();
    };
  };
  toggle('labelsBtn', 'showLabels', styleGraph);
  toggle('followsBtn', 'showFollows', styleGraph);
  toggle('origenBtn', 'showOrigen', styleGraph);
  toggle('hullsBtn', 'showHulls', drawHulls);

  // chintrolas slider SEPARACIÓN inyectado en la toolbar -bynd
  const toolbar = document.querySelector('.graph-toolbar');
  if (toolbar && !document.getElementById('sepRange')) {
    const wrap = document.createElement('label');
    wrap.id = 'sepWrap';
    wrap.title = 'Separación entre constelaciones';
    wrap.style.cssText = 'display:flex;align-items:center;gap:6px;background:var(--bg);border:1px solid var(--dim);' +
      'padding:0 8px;font-family:var(--mono);font-size:10px;letter-spacing:0.15em;color:var(--fg);text-transform:uppercase;';
    wrap.innerHTML = 'SEP <input type="range" id="sepRange" min="0.4" max="3" step="0.1" ' +
      'style="width:90px;accent-color:#E8FF00;cursor:pointer;"><span id="sepVal" style="min-width:28px;color:var(--accent)"></span>';
    toolbar.appendChild(wrap);
  }
  const sepRange = document.getElementById('sepRange');
  if (sepRange) {
    sepRange.value = CONST.separation;
    document.getElementById('sepVal').textContent = `×${CONST.separation.toFixed(1)}`;
    sepRange.oninput = () => {
      CONST.separation = parseFloat(sepRange.value);
      document.getElementById('sepVal').textContent = `×${CONST.separation.toFixed(1)}`;
      const link = simulation?.force('link');
      if (link) link.distance(link.distance());   // re-evalua distancias con la nueva separacion
      if (!state.frozen) simulation?.alpha(0.5).restart();
    };
  }

  const colorBtn = document.getElementById('colorBtn');
  if (colorBtn) {
    const paint = () => {
      colorBtn.textContent = state.colorMode === 'network' ? 'COLOR: RED' : 'COLOR: STATUS';
      colorBtn.classList.toggle('active', state.colorMode === 'network');
      document.getElementById('legendStatus')?.classList.toggle('hidden', state.colorMode === 'network');
      document.getElementById('legendNetwork')?.classList.toggle('hidden', state.colorMode !== 'network');
    };
    paint();
    colorBtn.onclick = () => {
      state.colorMode = state.colorMode === 'network' ? 'status' : 'network';
      paint();
      styleGraph();
    };
  }

  window.onresize = () => {
    if (!simulation) return;
    const { width, height } = svg.node().getBoundingClientRect();
    simulation.force('center', d3.forceCenter(width / 2, height / 2));
    simulation.alpha(0.3).restart();
  };
}

// ─── ENTRY POINT ─────────────────────────────────────────
// extras = { followedBy: [{username, connection}], red: [{username, score, ...}] }
function buildDashboard(rows, extras = {}) {
  const { nodes, links } = buildGraph(rows, extras.followedBy, extras.red);
  if (!nodes.length) {
    showToast('no nodes in result');
    return;
  }

  state.nodes = nodes;
  state.links = links;
  state.hasFollowData = (extras.followedBy || []).length > 0;
  const idx = indexGraph(nodes, links);
  Object.assign(state, idx);
  state.deadSet = computeDeadFamilies();
  const { nets, netOf, bodies, groupOf } = computeNetworks();
  state.nets = nets;
  state.netOf = netOf;
  state.bodies = bodies;
  state.groupOf = groupOf;
  state.roles = computeRoles();
  state.focusNet = null;
  state.selectedId = null;
  state.pathIds = new Set();
  state.pathOrdered = [];
  state.filter = 'all';

  initSvg();
  render();
  renderStats();
  renderNetworks();
  renderNodeInfo();
  wireDashboardUI();
  runSearch();
  setTimeout(applyHighlights, 100);
}

function destroyDashboard() {
  destroySimulation();
  Object.assign(state, {
    nodes: [], links: [],
    adj: new Map(), outAdj: new Map(), inAdj: new Map(),
    followOut: new Map(), followIn: new Map(), nodeMap: new Map(),
    deadSet: new Set(), nets: [], netOf: new Map(), focusNet: null,
    groupOf: new Map(), bodies: [], roles: new Map(),
    selectedId: null, pathIds: new Set(), pathOrdered: [],
  });
  allNodesSel = allLinksSel = null;
}

// ─── TOAST helper ────────────────────────────────────────
function showToast(msg) {
  const el = document.getElementById('toast');
  el.textContent = msg;
  el.classList.add('show');
  setTimeout(() => el.classList.remove('show'), 4500);
}

window.POLPO_DASHBOARD = { buildDashboard, destroyDashboard, showToast, _louvain: louvain, _state: state };

/* ═══════════════════════════════════════════════════════════
   POLPO :: NETWORK GALAXY  ·  galaxy.js
   Vista 3D del mismo grafo que dashboard.js, como galaxia.

   Reutiliza de dashboard.js (cargado antes): buildGraph,
   indexGraph, computeDeadFamilies, computeNetworks (Louvain),
   shortestPath, relationLabel, matchesFilter, nodeRadius, TIER…
   y el objeto global `state`. Solo cambia el render, así que
   las redes / tiers / dead families son idénticos a la vista 2D.

   Layout (FORMA: ESFERA, default)
   ───────────────────────────────
     SOL      = tú (self). Si pones SELF_USERNAME en config.js y
                ese user aparece en los datos, se funde con el sol.
     DISTANCIA 3D AL SOL = tiempo desde el follow.  Fecha que se usa, en orden:
                  followed_at → mutual_checked_at → red.checked_at
                  → last_updated → mediana de sus vecinos (inferida)
                Sin ninguna fecha → banda exterior "sin fecha".
                Escala LOG (default; separa bien lo reciente) o LINEAL.
     DIRECCIÓN = su red. Cada comunidad de Louvain con ≥ 3 miembros
                es un BRAZO: un cono que sale del sol hacia una
                dirección del cielo. Redes conectadas quedan con
                direcciones vecinas; los brazos se enroscan alrededor
                del eje Y conforme se alejan. Los sueltos toman la
                dirección promedio de sus vecinos, o una fija por hash.
     FORMA: DISCO = la versión plana (ángulo en el plano + grosor).

   PATH    pasa por ti (nodo virtual unido a quien sigues / te sigue),
           así dos mutuals tuyos quedan a 2 saltos. Lógica en dashboard.js.
   Todo es determinista (seed = hash del username): recargar no
   reacomoda la galaxia.

   RAYOS   todos conectados al sol (TODOS) o solo a quien sigues
           (SIGUES), o apagados.
   ANILLOS órbitas de tiempo: 1 día, 1 sem, 1 mes, 3 meses…
   ═══════════════════════════════════════════════════════════ */

(function () {
"use strict";

if (!window.THREE) {
  console.error('galaxy.js: three.js no cargó');
  return;
}

const CFG = window.POLPO_NETWORK_CONFIG || {};
const SELF_ID = String(CFG.SELF_USERNAME || '').trim().replace(/^@/, '');
const DAY = 864e5;

// ─── CONFIG VISUAL ───────────────────────────────────────
const GX = {
  R0: 42,            // radio de lo recién seguido (para no meterse en el sol)
  RMAX: 640,         // radio del follow más viejo
  UNDATED: 1.14,     // banda exterior para sin fecha (× RMAX)
  twist: 1.35,       // qué tanto se enrolla un brazo (rad por unidad de log)
  armSpread: 0.28,   // ancho angular del brazo (fracción de su sector)
  thick: 0.045,      // grosor del disco ∝ radio (solo FORMA: DISCO)
  twist3: 0.75,      // remolino de los brazos en la esfera (rad por unidad de log, eje Y)
  sizeK: 1150,       // tamaño de estrella en pantalla
  dimAlpha: 0.07,
  rotateSpeed: 0.28,
};

// cámara inicial con toda la galaxia en cuadro
const HOME_CAM = (aspect = 1.6) => {
  const k = aspect < 1 ? clamp(0.92 / aspect, 1, 2) : 1;   // pantallas angostas: alejarse
  if (gx.shape === 'disc') return [0, GX.RMAX * 1.12 * k, GX.RMAX * 1.62 * k];
  const d = new THREE.Vector3(0.38, 0.42, 1).normalize().multiplyScalar(GX.RMAX * 2.15 * k);
  return [d.x, d.y, d.z];
};

const RING_MARKS = [
  [1, '1 día'], [7, '1 semana'], [30, '1 mes'], [90, '3 meses'], [180, '6 meses'],
  [365, '1 año'], [730, '2 años'], [1095, '3 años'], [1460, '4 años'], [1826, '5 años'],
  [2557, '7 años'], [3652, '10 años'],
];

// ─── GALAXY STATE ────────────────────────────────────────
const gx = {
  order: [], idx: new Map(), time: new Map(), seeds: [],
  arms: [], armOf: new Map(),
  pos: null, anim: null, fly: null,
  maxDays: 1, scale: 'log', rays: 'all',
  shape: 'sphere',        // 'sphere' (volumen real: distancia 3D = tiempo) | 'disc'
  showRings: true, autoRotate: true,
  hoverId: null, alpha: null,
  followPairs: [], origenPairs: [], rayIdx: [],
  labelsDirty: true, labelItems: [], labelPool: [],
  raf: 0, ro: null, clock: null,
  // three
  renderer: null, scene: null, camera: null, controls: null,
  stars: null, starGeo: null, starMat: null,
  followLines: null, origenLines: null, rayLines: null, hlLines: null,
  ringGroup: null, ringLabels: [], marker: null, hoverMarker: null,
  sun: null, sunHalo: null, sunCore: null, bg: null, disc: null,
};

// ─── UTILS ───────────────────────────────────────────────
function hashStr(s) {
  let h = 2166136261 >>> 0;
  for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
  return h >>> 0;
}
function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function gauss(rnd) {
  const u = Math.max(1e-9, rnd()), v = rnd();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const ease = t => t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
const idOf = x => (x && x.id) || x;

function parseT(s) {
  if (!s) return NaN;
  const t = Date.parse(s);
  return Number.isFinite(t) ? t : NaN;
}

function fmtAge(days) {
  if (days == null || !Number.isFinite(days)) return 'sin fecha';
  if (days < 1) { const h = Math.max(1, Math.round(days * 24)); return `${h} h`; }
  if (days < 14) { const d = Math.round(days); return `${d} ${d === 1 ? 'día' : 'días'}`; }
  if (days < 60) { const w = Math.round(days / 7); return `${w} ${w === 1 ? 'semana' : 'semanas'}`; }
  if (days < 365) { const m = Math.round(days / 30.44); return `${m} ${m === 1 ? 'mes' : 'meses'}`; }
  const y = days / 365.25;
  const ys = y < 3 ? y.toFixed(1) : Math.round(y);
  return `${ys} ${ys == 1 ? 'año' : 'años'}`;
}

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
}

// ─── TIEMPO POR NODO ─────────────────────────────────────
function computeTimes() {
  const now = Date.now();
  const time = new Map();

  state.nodes.forEach(n => {
    const rec = { t: NaN, src: null, inferred: false, age: null };
    const tryF = (v, label) => {
      if (Number.isFinite(rec.t)) return;
      const x = parseT(v);
      if (Number.isFinite(x)) { rec.t = x; rec.src = label; }
    };
    tryF(n.followed_at, 'followed_at');
    tryF(n.mutual_checked_at, 'mutual_checked_at');
    tryF(n.red && n.red.checked_at, 'checked_at (red_perfil)');
    tryF(n.last_updated, 'last_updated');
    time.set(n.id, rec);
  });

  // inferir de vecinos (mediana) — externals y origins casi nunca traen fecha
  for (let pass = 0; pass < 4; pass++) {
    const upd = [];
    state.nodes.forEach(n => {
      if (n.id === SELF_ID) return;
      const rec = time.get(n.id);
      if (Number.isFinite(rec.t)) return;
      const ts = [];
      state.adj.get(n.id)?.forEach(m => {
        if (m === SELF_ID) return;
        const r = time.get(m);
        if (r && Number.isFinite(r.t)) ts.push(r.t);
      });
      if (ts.length) {
        ts.sort((a, b) => a - b);
        upd.push([n.id, ts[ts.length >> 1]]);
      }
    });
    if (!upd.length) break;
    upd.forEach(([id, t]) => {
      const rec = time.get(id);
      rec.t = t; rec.src = 'inferida (vecinos)'; rec.inferred = true;
    });
  }

  let maxDays = 1;
  time.forEach((rec, id) => {
    if (!Number.isFinite(rec.t) || id === SELF_ID) return;
    rec.age = Math.max(0, (now - rec.t) / DAY);
    if (rec.age > maxDays) maxDays = rec.age;
  });
  gx.time = time;
  gx.maxDays = maxDays;
}

function radiusOf(age, scale) {
  if (age == null) return null;
  const f = scale === 'log'
    ? Math.log1p(age) / Math.log1p(gx.maxDays)
    : age / gx.maxDays;
  return GX.R0 + (GX.RMAX - GX.R0) * clamp(f, 0, 1);
}

// ─── BRAZOS (una comunidad = un brazo) ───────────────────
function computeArms() {
  const arms = [];
  state.bodies.forEach(b => {
    const ids = b.ids.filter(id => id !== SELF_ID);
    if (ids.length < 3) return;
    arms.push({ key: b.key, ids, net: b.net, size: ids.length });
  });
  arms.sort((a, b) => b.size - a.size);

  // intercalar grande/chico para que los brazos grandes no queden pegados
  const ordered = [];
  for (let lo = 0, hi = arms.length - 1; lo <= hi;) {
    ordered.push(arms[lo++]);
    if (lo <= hi) ordered.push(arms[hi--]);
  }
  const w = a => Math.pow(a.size, 0.7);
  const W = ordered.reduce((s, a) => s + w(a), 0) || 1;
  let acc = hashStr('polpo') % 628 / 100;  // giro inicial fijo
  ordered.forEach(a => {
    const sector = w(a) / W * Math.PI * 2;
    a.base = acc + sector / 2;
    a.spread = clamp(sector * GX.armSpread, 0.035, 0.5);
    acc += sector;
  });

  const armOf = new Map();
  arms.forEach(a => a.ids.forEach(id => armOf.set(id, a)));
  gx.arms = arms;
  gx.armOf = armOf;

  sphereArmDirs(ordered, w, W);
}

// En la esfera cada brazo es una DIRECCIÓN desde el sol (un cono que sale
// hacia afuera). Arranque en espiral de Fibonacci y luego una relajación:
// brazos conectados se atraen (∝ log de # aristas entre ellos), todos se
// repelen según su tamaño. Así redes relacionadas quedan vecinas en el cielo.
function sphereArmDirs(ordered, w, W) {
  const K = ordered.length;
  if (!K) return;
  const golden = Math.PI * (3 - Math.sqrt(5));
  const off = hashStr('polpo') % 628 / 100;
  ordered.forEach(a => {
    const frac = w(a) / W;
    a.cap = Math.acos(clamp(1 - 2 * frac, -1, 1));       // radio angular de un casquete con ese % del cielo
    a.spread3 = clamp(a.cap * 0.5, 0.07, 0.55);
  });
  const P = ordered.map((a, k) => {
    const y = K === 1 ? 0.25 : 1 - 2 * (k + 0.5) / K;
    const r = Math.sqrt(Math.max(0, 1 - y * y));
    const f = k * golden + off;
    return new THREE.Vector3(Math.cos(f) * r, y * 0.9, Math.sin(f) * r).normalize();
  });

  const ix = new Map(ordered.map((a, k) => [a, k]));
  const cnt = new Map();
  state.links.forEach(l => {
    const A = gx.armOf.get(idOf(l.source)), B = gx.armOf.get(idOf(l.target));
    if (!A || !B || A === B) return;
    const a = ix.get(A), b = ix.get(B);
    const key = Math.min(a, b) * 65536 + Math.max(a, b);
    cnt.set(key, (cnt.get(key) || 0) + 1);
  });
  const pairs = Array.from(cnt, ([key, k]) => [Math.floor(key / 65536), key % 65536, Math.log1p(k)]);

  const F = P.map(() => new THREE.Vector3());
  const d = new THREE.Vector3();
  for (let it = 0; it < 220; it++) {
    const cool = 1 - it / 220;
    F.forEach(f => f.set(0, 0, 0));
    for (let i = 0; i < K; i++) {
      for (let j = i + 1; j < K; j++) {
        d.subVectors(P[i], P[j]);
        const len2 = Math.max(1e-4, d.lengthSq());
        const want = ordered[i].cap + ordered[j].cap;
        const rep = 0.006 * (0.3 + want * want) / len2;
        F[i].addScaledVector(d, rep);
        F[j].addScaledVector(d, -rep);
      }
    }
    for (const [a, b, wt] of pairs) {
      d.subVectors(P[b], P[a]);
      const minD = ordered[a].cap + ordered[b].cap;
      if (d.length() < minD) continue;
      F[a].addScaledVector(d, 0.03 * wt);
      F[b].addScaledVector(d, -0.03 * wt);
    }
    for (let i = 0; i < K; i++) {
      const f = F[i];
      const L = f.length();
      if (L > 0.12) f.multiplyScalar(0.12 / L);
      P[i].addScaledVector(f, cool).normalize();
    }
  }

  ordered.forEach((a, k) => {
    const dir = P[k];
    const up = Math.abs(dir.y) < 0.95 ? new THREE.Vector3(0, 1, 0) : new THREE.Vector3(1, 0, 0);
    const t1 = new THREE.Vector3().crossVectors(dir, up).normalize();
    const t2 = new THREE.Vector3().crossVectors(dir, t1).normalize();
    a.dir = dir; a.t1 = t1; a.t2 = t2;
  });
}

// ─── LAYOUT ──────────────────────────────────────────────
function computeLayout(scale) {
  return gx.shape === 'disc' ? computeLayoutDisc(scale) : computeLayoutSphere(scale);
}

function nodeRadiusAt(n, i, scale) {
  const r = radiusOf(gx.time.get(n.id)?.age, scale);
  return r == null ? GX.RMAX * GX.UNDATED + gx.seeds[i].u2 * 30 : r;
}

// ESFERA: |posición| = radio del tiempo (distancia 3D real al sol);
// la dirección la pone su red; los brazos se enroscan alrededor del eje Y.
function computeLayoutSphere(scale) {
  const N = gx.order.length;
  const out = new Float32Array(N * 3);
  const rad = new Float32Array(N);
  const dir = new Float32Array(N * 3);
  const has = new Uint8Array(N);

  gx.order.forEach((n, i) => {
    const s = gx.seeds[i];
    rad[i] = nodeRadiusAt(n, i, scale);
    const a = gx.armOf.get(n.id);
    if (!a || !a.dir) return;
    const sp = a.spread3;
    let x = a.dir.x + (a.t1.x * s.ga + a.t2.x * s.gb) * sp;
    let y = a.dir.y + (a.t1.y * s.ga + a.t2.y * s.gb) * sp;
    let z = a.dir.z + (a.t1.z * s.ga + a.t2.z * s.gb) * sp;
    const L = Math.hypot(x, y, z) || 1;
    dir[i * 3] = x / L; dir[i * 3 + 1] = y / L; dir[i * 3 + 2] = z / L;
    has[i] = 1;
  });

  // sueltos: dirección promedio de sus vecinos ya ubicados (2 pasadas)
  for (let pass = 0; pass < 2; pass++) {
    gx.order.forEach((n, i) => {
      if (has[i] === 1) return;
      let x = 0, y = 0, z = 0, c = 0;
      state.adj.get(n.id)?.forEach(m => {
        const j = gx.idx.get(m);
        if (j == null || !has[j] || m === SELF_ID) return;
        x += dir[j * 3]; y += dir[j * 3 + 1]; z += dir[j * 3 + 2]; c++;
      });
      const L = Math.hypot(x, y, z);
      if (!c || L < 0.05) return;
      const s = gx.seeds[i];
      x = x / L + s.ga * 0.14; y = y / L + s.gy * 0.14; z = z / L + s.gb * 0.14;
      const L2 = Math.hypot(x, y, z) || 1;
      dir[i * 3] = x / L2; dir[i * 3 + 1] = y / L2; dir[i * 3 + 2] = z / L2;
      has[i] = 2;
    });
  }

  gx.order.forEach((n, i) => {
    if (n.id === SELF_ID) return;   // se queda en 0,0,0 (el sol)
    const s = gx.seeds[i];
    let x, y, z;
    if (has[i]) { x = dir[i * 3]; y = dir[i * 3 + 1]; z = dir[i * 3 + 2]; }
    else {
      // sin red ni vecinos: dirección uniforme en la esfera
      y = 2 * s.u - 1;
      const rr = Math.sqrt(1 - y * y), f = 2 * Math.PI * s.u3;
      x = rr * Math.cos(f); z = rr * Math.sin(f);
    }
    const r = rad[i];
    const tw = GX.twist3 * Math.log1p(r / GX.R0);
    const c = Math.cos(tw), sn = Math.sin(tw);
    out[i * 3] = (x * c - z * sn) * r;
    out[i * 3 + 1] = y * r;
    out[i * 3 + 2] = (x * sn + z * c) * r;
  });
  return out;
}

// DISCO: la versión plana original (radio en el plano + grosor)
function computeLayoutDisc(scale) {
  const N = gx.order.length;
  const out = new Float32Array(N * 3);
  const rad = new Float32Array(N);
  const th = new Float32Array(N).fill(NaN);

  gx.order.forEach((n, i) => {
    const s = gx.seeds[i];
    const r = nodeRadiusAt(n, i, scale);
    rad[i] = r;
    const arm = gx.armOf.get(n.id);
    if (arm) th[i] = arm.base + GX.twist * Math.log1p(r / GX.R0) + s.ga * arm.spread;
  });

  // sueltos: ángulo promedio de sus vecinos ya ubicados (2 pasadas)
  for (let pass = 0; pass < 2; pass++) {
    gx.order.forEach((n, i) => {
      if (!Number.isNaN(th[i]) && (pass === 0 || !gx.seeds[i].loose)) return;
      let sx = 0, sy = 0, c = 0;
      state.adj.get(n.id)?.forEach(m => {
        const j = gx.idx.get(m);
        if (j == null || Number.isNaN(th[j]) || m === SELF_ID) return;
        sx += Math.cos(th[j]); sy += Math.sin(th[j]); c++;
      });
      if (c) { th[i] = Math.atan2(sy, sx) + gx.seeds[i].ga * 0.12; gx.seeds[i].loose = true; }
    });
  }

  gx.order.forEach((n, i) => {
    if (n.id === SELF_ID) return;   // se queda en 0,0,0 (el sol)
    const s = gx.seeds[i];
    const t = Number.isNaN(th[i]) ? s.u * Math.PI * 2 : th[i];
    const r = rad[i];
    out[i * 3] = Math.cos(t) * r;
    out[i * 3 + 1] = s.gy * (3 + GX.thick * r);
    out[i * 3 + 2] = Math.sin(t) * r;
  });
  return out;
}

// ─── COLORES ─────────────────────────────────────────────
function starColor(d) {
  if (state.colorMode === 'network') {
    const net = state.netOf.get(d.id);
    return net ? TIER[net.tier].color : '#3a3a3a';
  }
  if (state.deadSet.has(d.id)) return DEAD_COLOR;
  if (d.ghost) return '#7a7a7a';
  if (d.mutual) return '#E8FF00';
  if (d.kind === 'seen') return '#FF00B3';
  if (d.kind === 'external') return '#9a9a9a';
  if (DEAD_STATUSES.has(d.status)) return '#4a4a4a';
  return '#f5f5f5';
}
function starHollow(d) {
  return d.ghost || d.kind === 'seen';
}

// ─── SHADERS ─────────────────────────────────────────────
const STAR_VS = `
  attribute float aSize;
  attribute float aAlpha;
  attribute float aHollow;
  attribute vec3 aColor;
  uniform float uK;
  uniform float uMin;
  uniform float uNear;   // profundidad: lo del fondo de la esfera se apaga
  uniform float uFar;
  varying vec3 vColor;
  varying float vAlpha;
  varying float vHollow;
  void main() {
    vec4 mv = modelViewMatrix * vec4(position, 1.0);
    float s = aSize * uK / max(1.0, -mv.z);
    gl_PointSize = clamp(s, uMin, 96.0);
    gl_Position = projectionMatrix * mv;
    vColor = aColor;
    float depth = 1.0 - 0.72 * smoothstep(uNear, uFar, -mv.z);
    vAlpha = aAlpha * depth * (s < uMin ? max(0.35, s / uMin) : 1.0);
    vHollow = aHollow;
  }
`;
const STAR_FS = `
  varying vec3 vColor;
  varying float vAlpha;
  varying float vHollow;
  void main() {
    vec2 c = gl_PointCoord - 0.5;
    float d = length(c) * 2.0;
    if (d > 1.0) discard;
    float a;
    if (vHollow > 0.5) {
      float ring = 1.0 - smoothstep(0.06, 0.15, abs(d - 0.45));
      a = ring * 0.95 + pow(1.0 - d, 3.0) * 0.15;
    } else {
      float core = 1.0 - smoothstep(0.24, 0.38, d);
      float glow = pow(1.0 - d, 2.4) * 0.55;
      a = core + glow;
    }
    a *= vAlpha;
    if (a < 0.008) discard;
    gl_FragColor = vec4(vColor * a, 1.0);
  }
`;

function makeStarMaterial(pr) {
  return new THREE.ShaderMaterial({
    uniforms: {
      uK: { value: GX.sizeK * pr }, uMin: { value: 2.2 * pr },
      uNear: { value: 1e8 }, uFar: { value: 1e9 },     // sin atenuar hasta que el loop lo ajuste
    },
    vertexShader: STAR_VS,
    fragmentShader: STAR_FS,
    transparent: true,
    depthWrite: false,
    blending: THREE.AdditiveBlending,
  });
}

function glowTexture(stops) {
  const c = document.createElement('canvas');
  c.width = c.height = 256;
  const g = c.getContext('2d');
  const grd = g.createRadialGradient(128, 128, 0, 128, 128, 128);
  stops.forEach(([o, col]) => grd.addColorStop(o, col));
  g.fillStyle = grd;
  g.fillRect(0, 0, 256, 256);
  const tex = new THREE.CanvasTexture(c);
  return tex;
}

// ─── ESCENA ──────────────────────────────────────────────
function initScene() {
  const stage = document.getElementById('galaxyStage');
  stage.innerHTML = '';
  const w = stage.clientWidth || 800, h = stage.clientHeight || 600;
  const pr = Math.min(window.devicePixelRatio || 1, 2);

  const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true, preserveDrawingBuffer: false });
  renderer.setPixelRatio(pr);
  renderer.setSize(w, h);
  renderer.setClearColor(0x000000, 0);
  stage.appendChild(renderer.domElement);

  const scene = new THREE.Scene();
  // niebla negra = con blending aditivo, lo lejano se apaga (cue de profundidad para las líneas)
  scene.fog = new THREE.Fog(0x000000, 1e8, 1e9);
  const camera = new THREE.PerspectiveCamera(52, w / h, 1, 20000);
  camera.position.set(...HOME_CAM(w / h));

  const controls = new THREE.OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;
  controls.dampingFactor = 0.08;
  controls.rotateSpeed = 0.6;
  controls.zoomSpeed = 0.9;
  controls.minDistance = 20;
  controls.maxDistance = GX.RMAX * 5;
  controls.autoRotate = gx.autoRotate;
  controls.autoRotateSpeed = GX.rotateSpeed;
  controls.target.set(0, 0, 0);

  Object.assign(gx, { renderer, scene, camera, controls, pr });

  // fondo: estrellas lejanas (decoración, no son datos)
  {
    const rnd = mulberry32(7);
    const M = 2200, p = new Float32Array(M * 3);
    for (let i = 0; i < M; i++) {
      const u = rnd() * 2 - 1, t = rnd() * Math.PI * 2, r = 4500 + rnd() * 3000;
      const s = Math.sqrt(1 - u * u);
      p[i * 3] = s * Math.cos(t) * r; p[i * 3 + 1] = u * r; p[i * 3 + 2] = s * Math.sin(t) * r;
    }
    const g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.BufferAttribute(p, 3));
    gx.bg = new THREE.Points(g, new THREE.PointsMaterial({
      color: 0x5a5a66, size: 1.3, sizeAttenuation: false, transparent: true, opacity: 0.7, depthWrite: false, fog: false,
    }));
    scene.add(gx.bg);
  }

  // halo tenue del disco
  {
    const tex = glowTexture([[0, 'rgba(255,240,200,0.55)'], [0.18, 'rgba(255,200,120,0.18)'], [0.55, 'rgba(120,110,160,0.05)'], [1, 'rgba(0,0,0,0)']]);
    const m = new THREE.MeshBasicMaterial({ map: tex, transparent: true, depthWrite: false, blending: THREE.AdditiveBlending, opacity: 0.55, side: THREE.DoubleSide, fog: false });
    gx.disc = new THREE.Mesh(new THREE.PlaneGeometry(GX.RMAX * 2.5, GX.RMAX * 2.5), m);
    gx.disc.rotation.x = -Math.PI / 2;
    gx.disc.visible = gx.shape === 'disc';
    scene.add(gx.disc);
  }

  // el SOL (self)
  {
    const tex = glowTexture([[0, 'rgba(255,255,255,1)'], [0.12, 'rgba(255,246,200,1)'], [0.3, 'rgba(255,200,80,0.55)'], [0.6, 'rgba(255,140,0,0.12)'], [1, 'rgba(0,0,0,0)']]);
    gx.sun = new THREE.Sprite(new THREE.SpriteMaterial({ map: tex, blending: THREE.AdditiveBlending, depthWrite: false, transparent: true, fog: false }));
    gx.sun.scale.set(110, 110, 1);
    scene.add(gx.sun);
    gx.sunHalo = new THREE.Sprite(new THREE.SpriteMaterial({ map: tex, blending: THREE.AdditiveBlending, depthWrite: false, transparent: true, opacity: 0.22, fog: false }));
    gx.sunHalo.scale.set(330, 330, 1);
    scene.add(gx.sunHalo);
    gx.sunCore = new THREE.Mesh(new THREE.SphereGeometry(8, 24, 16), new THREE.MeshBasicMaterial({ color: 0xfff6d8, fog: false }));
    scene.add(gx.sunCore);
  }

  gx.clock = new THREE.Clock();
}

// ─── BUFFERS ─────────────────────────────────────────────
function buildStars() {
  const N = gx.order.length;
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(gx.pos.slice(), 3));
  geo.setAttribute('aColor', new THREE.BufferAttribute(new Float32Array(N * 3), 3));
  geo.setAttribute('aSize', new THREE.BufferAttribute(new Float32Array(N), 1));
  geo.setAttribute('aAlpha', new THREE.BufferAttribute(new Float32Array(N).fill(1), 1));
  geo.setAttribute('aHollow', new THREE.BufferAttribute(new Float32Array(N), 1));
  gx.starGeo = geo;
  gx.starMat = makeStarMaterial(gx.pr);
  gx.stars = new THREE.Points(geo, gx.starMat);
  gx.stars.frustumCulled = false;
  gx.scene.add(gx.stars);

  // marcadores de selección / hover (un anillo cada uno)
  const mkMarker = (hex) => {
    const g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(3), 3));
    const c = new THREE.Color(hex);
    g.setAttribute('aColor', new THREE.BufferAttribute(new Float32Array([c.r, c.g, c.b]), 3));
    g.setAttribute('aSize', new THREE.BufferAttribute(new Float32Array([20]), 1));
    g.setAttribute('aAlpha', new THREE.BufferAttribute(new Float32Array([1]), 1));
    g.setAttribute('aHollow', new THREE.BufferAttribute(new Float32Array([1]), 1));
    const p = new THREE.Points(g, makeStarMaterial(gx.pr));
    p.frustumCulled = false;
    p.visible = false;
    gx.scene.add(p);
    return p;
  };
  gx.marker = mkMarker('#E8FF00');
  gx.hoverMarker = mkMarker('#ffffff');

  styleStars();
}

function styleStars() {
  if (!gx.starGeo) return;
  const col = gx.starGeo.getAttribute('aColor');
  const size = gx.starGeo.getAttribute('aSize');
  const hol = gx.starGeo.getAttribute('aHollow');
  const c = new THREE.Color();
  gx.order.forEach((d, i) => {
    c.set(starColor(d));
    col.array[i * 3] = c.r; col.array[i * 3 + 1] = c.g; col.array[i * 3 + 2] = c.b;
    size.array[i] = d.id === SELF_ID ? 0 : nodeRadius(d) * (d.mutual ? 1.15 : 1);
    hol.array[i] = starHollow(d) ? 1 : 0;
  });
  col.needsUpdate = size.needsUpdate = hol.needsUpdate = true;
  styleLines();
}

function makeLineObj(pairsLen, dashed, opacity) {
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(Math.max(1, pairsLen) * 6), 3));
  g.setAttribute('color', new THREE.BufferAttribute(new Float32Array(Math.max(1, pairsLen) * 6), 3));
  g.setDrawRange(0, pairsLen * 2);
  const opts = { vertexColors: true, transparent: true, opacity, depthWrite: false, blending: THREE.AdditiveBlending };
  const m = dashed ? new THREE.LineDashedMaterial({ ...opts, dashSize: 5, gapSize: 5 }) : new THREE.LineBasicMaterial(opts);
  const l = new THREE.LineSegments(g, m);
  l.frustumCulled = false;
  return l;
}

function buildLines() {
  const fp = [], op = [];
  state.links.forEach(l => {
    const a = gx.idx.get(idOf(l.source)), b = gx.idx.get(idOf(l.target));
    if (a == null || b == null) return;
    if (l.types.has('follows')) fp.push([a, b, l]);
    if (l.types.has('origen')) op.push([a, b, l]);
  });
  gx.followPairs = fp;
  gx.origenPairs = op;

  gx.followLines = makeLineObj(fp.length, false, 0.42);
  gx.origenLines = makeLineObj(op.length, true, 0.4);
  gx.scene.add(gx.followLines, gx.origenLines);

  gx.rayLines = makeLineObj(gx.order.length, false, 1);
  gx.scene.add(gx.rayLines);

  gx.hlLines = makeLineObj(0, false, 0.95);
  gx.scene.add(gx.hlLines);

  rebuildRayIdx();
}

function rebuildRayIdx() {
  gx.rayIdx = [];
  if (gx.rays === 'off') return;
  gx.order.forEach((d, i) => {
    if (d.id === SELF_ID) return;
    if (gx.rays === 'yours' && !selfTie(d)) return;
    gx.rayIdx.push(i);
  });
  gx.rayLines.geometry.setDrawRange(0, gx.rayIdx.length * 2);
}

function writeLinePositions() {
  const P = gx.pos;
  const put = (obj, pairs) => {
    const arr = obj.geometry.getAttribute('position').array;
    pairs.forEach(([a, b], k) => {
      arr[k * 6] = P[a * 3]; arr[k * 6 + 1] = P[a * 3 + 1]; arr[k * 6 + 2] = P[a * 3 + 2];
      arr[k * 6 + 3] = P[b * 3]; arr[k * 6 + 4] = P[b * 3 + 1]; arr[k * 6 + 5] = P[b * 3 + 2];
    });
    obj.geometry.getAttribute('position').needsUpdate = true;
    obj.geometry.computeBoundingSphere();
  };
  put(gx.followLines, gx.followPairs);
  put(gx.origenLines, gx.origenPairs);
  gx.origenLines.computeLineDistances();

  const ra = gx.rayLines.geometry.getAttribute('position').array;
  gx.rayIdx.forEach((i, k) => {
    ra[k * 6] = 0; ra[k * 6 + 1] = 0; ra[k * 6 + 2] = 0;
    ra[k * 6 + 3] = P[i * 3]; ra[k * 6 + 4] = P[i * 3 + 1]; ra[k * 6 + 5] = P[i * 3 + 2];
  });
  gx.rayLines.geometry.getAttribute('position').needsUpdate = true;
}

function styleLines() {
  if (!gx.followLines) return;
  const alpha = gx.alpha;
  const cols = gx.starGeo.getAttribute('aColor').array;
  const dimOf = i => (alpha ? alpha[i] < 0.5 : false);
  const c = new THREE.Color();

  const paint = (obj, pairs, k0) => {
    const arr = obj.geometry.getAttribute('color').array;
    pairs.forEach(([a, b, l], k) => {
      const f = (dimOf(a) || dimOf(b)) ? 0.06 : k0;
      if (linkIsDead(l)) {
        c.set(DEAD_COLOR);
        for (let j = 0; j < 2; j++) { arr[k * 6 + j * 3] = c.r * f; arr[k * 6 + j * 3 + 1] = c.g * f; arr[k * 6 + j * 3 + 2] = c.b * f; }
        return;
      }
      // cada punta toma el color de su estrella (mínimo gris para que no desaparezca)
      [a, b].forEach((i, j) => {
        arr[k * 6 + j * 3] = Math.max(0.18, cols[i * 3]) * f;
        arr[k * 6 + j * 3 + 1] = Math.max(0.18, cols[i * 3 + 1]) * f;
        arr[k * 6 + j * 3 + 2] = Math.max(0.18, cols[i * 3 + 2]) * f;
      });
    });
    obj.geometry.getAttribute('color').needsUpdate = true;
  };
  paint(gx.followLines, gx.followPairs, 0.55);
  paint(gx.origenLines, gx.origenPairs, 0.4);

  // rayos: brillan cerca del sol y se apagan hacia la estrella
  const ra = gx.rayLines.geometry.getAttribute('color').array;
  const many = gx.rayIdx.length > 1500 ? 0.55 : 1;
  gx.rayIdx.forEach((i, k) => {
    const d = gx.order[i];
    const dim = dimOf(i);
    const base = (d.mutual ? 0.16 : isYours(d) ? 0.1 : 0.05) * many * (dim ? 0.15 : 1);
    const tip = base * 0.45;
    for (let j = 0; j < 3; j++) {
      const ch = Math.max(0.25, cols[i * 3 + j]);
      ra[k * 6 + j] = ch * base;
      ra[k * 6 + 3 + j] = ch * tip;
    }
  });
  gx.rayLines.geometry.getAttribute('color').needsUpdate = true;

  gx.followLines.visible = !!state.showFollows;
  gx.origenLines.visible = !!state.showOrigen;
  gx.rayLines.visible = gx.rays !== 'off';
}

function writeStarPositions() {
  const a = gx.starGeo.getAttribute('position');
  a.array.set(gx.pos);
  a.needsUpdate = true;
  writeLinePositions();
  updateHlLines();
  updateMarkers();
  gx.labelsDirty = true;
}

// ─── ANILLOS DE TIEMPO ───────────────────────────────────
function buildRings() {
  if (gx.ringGroup) {
    gx.ringGroup.traverse(o => { o.geometry?.dispose(); o.material?.dispose(); });
    gx.scene.remove(gx.ringGroup);
  }
  const group = new THREE.Group();
  gx.ringLabels = [];
  const marks = RING_MARKS.filter(([d]) => d <= gx.maxDays * 1.02);
  let last = -1e9;
  const mkRing = (r, label, color, opacity) => {
    const pts = [];
    for (let k = 0; k <= 160; k++) {
      const t = k / 160 * Math.PI * 2;
      // esfera: círculo en XY que se gira cada frame hacia la cámara (= silueta de la cáscara de ese radio)
      // disco: círculo en el plano del disco
      pts.push(gx.shape === 'disc'
        ? new THREE.Vector3(Math.cos(t) * r, 0, Math.sin(t) * r)
        : new THREE.Vector3(Math.cos(t) * r, Math.sin(t) * r, 0));
    }
    const g = new THREE.BufferGeometry().setFromPoints(pts);
    const line = new THREE.Line(g, new THREE.LineDashedMaterial({
      color, dashSize: 6, gapSize: 7, transparent: true, opacity, depthWrite: false, fog: false,
    }));
    line.computeLineDistances();
    group.add(line);
    gx.ringLabels.push({ r, text: label });
  };
  marks.forEach(([d, label]) => {
    const r = radiusOf(d, gx.scale);
    if (r - last < 22) return;
    last = r;
    mkRing(r, label, 0x3a3a3a, 0.9);
  });
  // borde: el follow más viejo
  const rMax = radiusOf(gx.maxDays, gx.scale);
  if (rMax - last > 14) mkRing(rMax, `máx · ${fmtAge(gx.maxDays)}`, 0x4d4d4d, 0.9);
  // sin fecha
  let undated = 0;
  gx.time.forEach((r, id) => { if (r.age == null && id !== SELF_ID) undated++; });
  if (undated) mkRing(GX.RMAX * GX.UNDATED + 15, 'sin fecha', 0x2a2a2a, 0.8);

  group.visible = gx.showRings;
  gx.ringGroup = group;
  gx.scene.add(group);
  gx.labelsDirty = true;
}

// ─── HIGHLIGHTS ──────────────────────────────────────────
function applyHighlights() {
  if (!gx.starGeo) return;
  const sel = state.selectedId;
  const path = state.pathIds;
  const search = (document.getElementById('searchInput')?.value || '').toLowerCase().trim();
  const focus = state.focusNet != null ? state.nets[state.focusNet] : null;
  const neighbors = sel ? (state.adj.get(sel) || new Set()) : null;

  const N = gx.order.length;
  if (!gx.alpha || gx.alpha.length !== N) gx.alpha = new Float32Array(N);
  gx.order.forEach((d, i) => {
    let dim = !matchesFilter(d);
    if (search && !d.id.toLowerCase().includes(search)) dim = true;
    if (focus && !focus.set.has(d.id)) dim = true;
    if (sel) dim = !(d.id === sel || neighbors.has(d.id));
    else if (path.size) dim = true;          // con path activo solo se ve el path
    if (path.has(d.id)) dim = false;
    gx.alpha[i] = dim ? GX.dimAlpha : 1;
  });
  gx.starGeo.getAttribute('aAlpha').array.set(gx.alpha);
  gx.starGeo.getAttribute('aAlpha').needsUpdate = true;

  styleLines();
  updateHlLines();
  updateMarkers();
  gx.labelsDirty = true;
}

// aristas resaltadas: las del nodo seleccionado (amarillo) y el path (rosa)
function updateHlLines() {
  if (!gx.hlLines) return;
  const segs = [];
  const sel = state.selectedId;
  const ordered = state.pathOrdered || [];
  const pathPairs = new Set();
  // el path se dibuja salto por salto (incluye los saltos por ti, que no son aristas del grafo)
  for (let i = 0; i < ordered.length - 1; i++) {
    pathPairs.add(`${ordered[i]}|${ordered[i + 1]}`);
    pathPairs.add(`${ordered[i + 1]}|${ordered[i]}`);
    segs.push([ordered[i], ordered[i + 1], 0xFF00B3]);
  }
  if (sel) {
    state.links.forEach(l => {
      const s = idOf(l.source), t = idOf(l.target);
      if (s !== sel && t !== sel) return;
      if (pathPairs.has(`${s}|${t}`)) return;
      if (!state.showFollows && !l.types.has('origen')) return;
      segs.push([s, t, l.types.has('follows') ? 0xE8FF00 : 0x8a9400]);
    });
    // su lazo contigo (rayo dorado)
    if (sel !== SELF_KEY && selfTie(state.nodeMap.get(sel)) && !pathPairs.has(`${SELF_KEY}|${sel}`)) {
      segs.push([SELF_KEY, sel, 0xffd36b]);
    }
  }

  const need = segs.length * 6;
  let g = gx.hlLines.geometry;
  if (g.getAttribute('position').array.length < need) {
    g.dispose();
    g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(need * 2), 3));
    g.setAttribute('color', new THREE.BufferAttribute(new Float32Array(need * 2), 3));
    gx.hlLines.geometry = g;
  }
  const pa = g.getAttribute('position').array, ca = g.getAttribute('color').array;
  const c = new THREE.Color();
  const P = gx.pos;
  const posOf = id => {
    const i = gx.idx.get(id);
    return i == null ? [0, 0, 0] : [P[i * 3], P[i * 3 + 1], P[i * 3 + 2]];
  };
  segs.forEach(([s, t, hex], k) => {
    const a = posOf(s), b = posOf(t);
    pa.set(a, k * 6); pa.set(b, k * 6 + 3);
    c.setHex(hex);
    ca[k * 6] = ca[k * 6 + 3] = c.r;
    ca[k * 6 + 1] = ca[k * 6 + 4] = c.g;
    ca[k * 6 + 2] = ca[k * 6 + 5] = c.b;
  });
  g.getAttribute('position').needsUpdate = true;
  g.getAttribute('color').needsUpdate = true;
  g.setDrawRange(0, segs.length * 2);
}

function updateMarkers() {
  const place = (marker, id, scale) => {
    const i = id != null ? gx.idx.get(id) : null;
    if (i == null || id === SELF_ID) { marker.visible = false; return; }
    const p = marker.geometry.getAttribute('position');
    p.array[0] = gx.pos[i * 3]; p.array[1] = gx.pos[i * 3 + 1]; p.array[2] = gx.pos[i * 3 + 2];
    p.needsUpdate = true;
    marker.geometry.getAttribute('aSize').array[0] = nodeRadius(gx.order[i]) * scale + 6;
    marker.geometry.getAttribute('aSize').needsUpdate = true;
    marker.visible = true;
  };
  if (!gx.marker) return;
  place(gx.marker, state.selectedId, 2.6);
  place(gx.hoverMarker, gx.hoverId !== state.selectedId ? gx.hoverId : null, 2.0);
}

// ─── ETIQUETAS ───────────────────────────────────────────
function rebuildLabelItems() {
  const items = [];
  const seen = new Set();
  const addStar = (id, cls) => {
    if (seen.has(id) || id === SELF_ID) return;
    const i = gx.idx.get(id);
    if (i == null) return;
    seen.add(id);
    const d = gx.order[i];
    items.push({ i, text: '@' + id, cls: cls || (d.mutual ? 'mutual' : ''), off: 'translate(-50%, 9px)' });
  };

  // orden = prioridad: si dos etiquetas chocan en pantalla, gana la que va antes
  items.push({ sun: true, text: SELF_ID ? '@' + SELF_ID : 'tú', cls: 'sun', off: 'translate(-50%, 34px)' });

  const sel = state.selectedId;
  if (sel) addStar(sel, 'sel');
  (state.pathOrdered || []).forEach(id => addStar(id, 'path'));
  if (gx.hoverId) addStar(gx.hoverId);

  if (gx.showRings) {
    gx.ringLabels.forEach(r => items.push({ ring: r.r, text: r.text, cls: 'ring', off: 'translate(5px, -50%)' }));
  }

  if (state.showLabels) {
    // nombres de las redes en el centro de su brazo
    state.nets.slice(0, 14).forEach(net => {
      if (state.focusNet != null && state.focusNet !== net.id) return;
      if (sel) return;
      let x = 0, y = 0, z = 0, c = 0;
      net.members.forEach(id => {
        const i = gx.idx.get(id);
        if (i == null || id === SELF_ID) return;
        x += gx.pos[i * 3]; y += gx.pos[i * 3 + 1]; z += gx.pos[i * 3 + 2]; c++;
      });
      if (!c) return;
      items.push({ xyz: [x / c, y / c + 18, z / c], text: `${TIER[net.tier].label} · @${net.name}`, cls: 'net', color: TIER[net.tier].color, off: 'translate(-50%, -50%)' });
    });

    if (sel) {
      Array.from(state.adj.get(sel) || []).slice(0, 40).forEach(id => addStar(id));
    } else if (state.focusNet != null) {
      const net = state.nets[state.focusNet];
      net.members.slice().sort((a, b) => nodeRadius(state.nodeMap.get(b)) - nodeRadius(state.nodeMap.get(a)))
        .slice(0, 50).forEach(id => addStar(id));
    } else {
      const search = (document.getElementById('searchInput')?.value || '').toLowerCase().trim();
      if (search) {
        gx.order.filter(d => d.id.toLowerCase().includes(search) && matchesFilter(d)).slice(0, 40).forEach(d => addStar(d.id));
      } else {
        state.nets.forEach(net => net.hubs.slice(0, 1).forEach(id => addStar(id)));
        gx.order.filter(d => d.mutual && matchesFilter(d))
          .sort((a, b) => nodeRadius(b) - nodeRadius(a))
          .slice(0, 45).forEach(d => addStar(d.id));
      }
    }
  }

  gx.labelItems = items.slice(0, 180);
  const box = document.getElementById('galaxyLabels');
  while (gx.labelPool.length < gx.labelItems.length) {
    const el = document.createElement('div');
    el.className = 'g-label';
    box.appendChild(el);
    gx.labelPool.push(el);
  }
  gx.labelPool.forEach((el, k) => {
    const it = gx.labelItems[k];
    if (!it) { el.style.display = 'none'; return; }
    el.style.display = '';
    el.className = 'g-label ' + (it.cls || '');
    el.textContent = it.text;
    el.style.color = it.color || '';
  });
  // medir una vez (para la anti-colisión por frame)
  gx.labelItems.forEach((it, k) => {
    const el = gx.labelPool[k];
    it.w = el.offsetWidth || it.text.length * 6;
    it.h = el.offsetHeight || 12;
    // caja relativa al punto proyectado, igual que el translate de `off`
    if (it.cls === 'net') { it.bx = -it.w / 2; it.by = -it.h / 2; }
    else if (it.ring != null) { it.bx = 5; it.by = -it.h / 2; }
    else if (it.sun) { it.bx = -it.w / 2; it.by = 34; }
    else { it.bx = -it.w / 2; it.by = 9; }
  });
  gx.labelsDirty = false;
}

const _v = new THREE.Vector3();
function drawLabels() {
  if (gx.labelsDirty) rebuildLabelItems();
  const cam = gx.camera;
  const w = gx.renderer.domElement.clientWidth, h = gx.renderer.domElement.clientHeight;
  const camDist = cam.position.distanceTo(gx.controls.target);
  // anillos: etiqueta en el punto del anillo más cercano a la cámara (proyectado al plano)
  const ang = Math.atan2(cam.position.z, cam.position.x);
  const placed = [];
  const PAD = 3;
  gx.labelItems.forEach((it, k) => {
    const el = gx.labelPool[k];
    if (it.sun) _v.set(0, 0, 0);
    else if (it.ring != null) {
      if (gx.shape === 'disc') _v.set(Math.cos(ang + 0.35) * it.ring, 0, Math.sin(ang + 0.35) * it.ring);
      else _v.set(Math.cos(-0.5) * it.ring, Math.sin(-0.5) * it.ring, 0).applyQuaternion(cam.quaternion);   // abajo-derecha del círculo
    }
    else if (it.xyz) _v.set(it.xyz[0], it.xyz[1], it.xyz[2]);
    else _v.set(gx.pos[it.i * 3], gx.pos[it.i * 3 + 1], gx.pos[it.i * 3 + 2]);
    const dist = cam.position.distanceTo(_v);
    _v.project(cam);
    if (_v.z > 1 || _v.x < -1.1 || _v.x > 1.1 || _v.y < -1.1 || _v.y > 1.1) { el.style.opacity = '0'; return; }
    const x = (_v.x * 0.5 + 0.5) * w, y = (-_v.y * 0.5 + 0.5) * h;
    const x0 = x + it.bx - PAD, y0 = y + it.by - PAD, x1 = x0 + it.w + PAD * 2, y1 = y0 + it.h + PAD * 2;
    for (let q = 0; q < placed.length; q++) {
      const b = placed[q];
      if (x0 < b[2] && x1 > b[0] && y0 < b[3] && y1 > b[1]) { el.style.opacity = '0'; return; }
    }
    placed.push([x0, y0, x1, y1]);
    let op = 1;
    if (!it.sun && !it.ring && it.cls !== 'sel' && it.cls !== 'path' && it.cls !== 'net') {
      op = clamp(1.6 - dist / (camDist * 1.25), 0.15, 1);
      if (it.i != null && gx.alpha && gx.alpha[it.i] < 0.5) op *= 0.25;
    }
    el.style.opacity = op.toFixed(2);
    el.style.transform = `translate(${x.toFixed(1)}px, ${y.toFixed(1)}px) ${it.off}`;
  });
}

// ─── PICKING ─────────────────────────────────────────────
const _m = new THREE.Matrix4();
function pickAt(clientX, clientY) {
  const el = gx.renderer.domElement;
  const rect = el.getBoundingClientRect();
  const mx = clientX - rect.left, my = clientY - rect.top;
  const w = rect.width, h = rect.height;
  _m.multiplyMatrices(gx.camera.projectionMatrix, gx.camera.matrixWorldInverse);
  const e = _m.elements;
  const P = gx.pos;
  const sizes = gx.starGeo.getAttribute('aSize').array;
  let best = null, bestD = Infinity;
  for (let i = 0; i < gx.order.length; i++) {
    if (sizes[i] === 0) continue;
    if (gx.alpha && gx.alpha[i] < 0.5) continue;
    const x = P[i * 3], y = P[i * 3 + 1], z = P[i * 3 + 2];
    const cw = e[3] * x + e[7] * y + e[11] * z + e[15];
    if (cw <= 0) continue;
    const sx = ((e[0] * x + e[4] * y + e[8] * z + e[12]) / cw * 0.5 + 0.5) * w;
    const sy = (-(e[1] * x + e[5] * y + e[9] * z + e[13]) / cw * 0.5 + 0.5) * h;
    const dx = sx - mx, dy = sy - my;
    const d2 = dx * dx + dy * dy;
    const px = clamp(sizes[i] * GX.sizeK / cw, 2.2, 96) * 0.5;
    const rad = Math.max(7, px * 0.6);
    if (d2 < rad * rad && d2 < bestD) { bestD = d2; best = i; }
  }
  return best == null ? null : gx.order[best].id;
}

// ─── TOOLTIP ─────────────────────────────────────────────
function tooltipHtml(d) {
  const fin = state.followIn.get(d.id)?.size || 0;
  const fout = state.followOut.get(d.id)?.size || 0;
  const deadTag = state.deadSet.has(d.id) ? ' · dead family' : '';
  const net = state.netOf.get(d.id);
  const kind = KIND_LABEL[d.kind] || (d.status || '—');
  const t = gx.time.get(d.id);
  const when = t?.age != null
    ? `hace ${fmtAge(t.age)}${t.inferred ? ' (inferida)' : ''}`
    : 'sin fecha';
  return `
    <div class="tooltip-name">@${escapeHtml(d.id)}</div>
    <div>${kind}${d.mutual ? ' · mutual' : ''}${deadTag}</div>
    <div style="color:#ffd36b;margin-top:2px;">☉ ${when}</div>
    <div style="color:var(--muted);margin-top:2px;">lo siguen ${fin} · sigue ${fout}</div>
    ${net ? `<div style="color:${TIER[net.tier].color};margin-top:2px;">red @${escapeHtml(net.name)} · ${TIER[net.tier].label}</div>` : ''}
    ${d.red ? `<div style="color:var(--muted);">score ${d.red.score}</div>` : ''}
  `;
}

// ─── CÁMARA ──────────────────────────────────────────────
function flyTo(target, dist, dur = 900) {
  const cam = gx.camera, ctl = gx.controls;
  const dir = cam.position.clone().sub(ctl.target).normalize();
  if (dir.y < 0.25) { dir.y = 0.35; dir.normalize(); }
  const toTarget = new THREE.Vector3(...target);
  const toPos = toTarget.clone().add(dir.multiplyScalar(dist));
  gx.fly = {
    t0: performance.now(), dur,
    fromPos: cam.position.clone(), toPos,
    fromTarget: ctl.target.clone(), toTarget,
  };
}
function flyToNode(id) {
  const i = gx.idx.get(id);
  if (i == null) return;
  flyTo([gx.pos[i * 3], gx.pos[i * 3 + 1], gx.pos[i * 3 + 2]], 170);
}
function flyToMembers(ids) {
  let x = 0, y = 0, z = 0, c = 0;
  const pts = [];
  ids.forEach(id => {
    const i = gx.idx.get(id);
    let p;
    if (id === SELF_KEY) p = [0, 0, 0];
    else if (i == null) return;
    else p = [gx.pos[i * 3], gx.pos[i * 3 + 1], gx.pos[i * 3 + 2]];
    pts.push(p); x += p[0]; y += p[1]; z += p[2]; c++;
  });
  if (!c) return;
  const cen = [x / c, y / c, z / c];
  let r = 0;
  pts.forEach(p => { r = Math.max(r, Math.hypot(p[0] - cen[0], p[1] - cen[1], p[2] - cen[2])); });
  flyTo(cen, clamp(r * 2.2, 140, GX.RMAX * 2));
}
function resetView() {
  gx.fly = {
    t0: performance.now(), dur: 900,
    fromPos: gx.camera.position.clone(), toPos: new THREE.Vector3(...HOME_CAM(gx.camera.aspect)),
    fromTarget: gx.controls.target.clone(), toTarget: new THREE.Vector3(0, 0, 0),
  };
}

// ─── LOOP ────────────────────────────────────────────────
function animate() {
  gx.raf = requestAnimationFrame(animate);
  const now = performance.now();
  const t = gx.clock.getElapsedTime();

  if (gx.anim) {
    const k = clamp((now - gx.anim.t0) / gx.anim.dur, 0, 1), e = ease(k);
    const { from, to } = gx.anim;
    for (let j = 0; j < gx.pos.length; j++) gx.pos[j] = from[j] + (to[j] - from[j]) * e;
    writeStarPositions();
    if (k >= 1) gx.anim = null;
  }

  if (gx.fly) {
    const k = clamp((now - gx.fly.t0) / gx.fly.dur, 0, 1), e = ease(k);
    gx.camera.position.lerpVectors(gx.fly.fromPos, gx.fly.toPos, e);
    gx.controls.target.lerpVectors(gx.fly.fromTarget, gx.fly.toTarget, e);
    if (k >= 1) gx.fly = null;
  }

  const pulse = 1 + Math.sin(t * 1.3) * 0.04;
  gx.sun.scale.set(110 * pulse, 110 * pulse, 1);
  gx.sunHalo.scale.set(330 / pulse, 330 / pulse, 1);
  if (gx.marker.visible) {
    const s = gx.marker.geometry.getAttribute('aAlpha');
    s.array[0] = 0.65 + Math.sin(t * 4) * 0.35;
    s.needsUpdate = true;
  }

  gx.controls.update();

  // profundidad: atenuar lo que queda detrás del sol (relativo a la distancia de cámara)
  const camD = gx.camera.position.length();
  const near = Math.max(1, camD - GX.RMAX * 0.55), far = camD + GX.RMAX * 1.25;
  gx.starMat.uniforms.uNear.value = near;
  gx.starMat.uniforms.uFar.value = far;
  gx.scene.fog.near = near;
  gx.scene.fog.far = far + GX.RMAX * 0.9;
  if (gx.ringGroup && gx.shape !== 'disc') gx.ringGroup.quaternion.copy(gx.camera.quaternion);

  gx.renderer.render(gx.scene, gx.camera);
  drawLabels();
}

// ─── INTERACCIÓN ─────────────────────────────────────────
function wireCanvas() {
  const el = gx.renderer.domElement;
  const stage = document.getElementById('galaxyStage');
  const tooltipEl = document.getElementById('tooltip');
  let down = null, pending = null, queued = false;

  el.addEventListener('pointerdown', e => { down = { x: e.clientX, y: e.clientY }; });
  el.addEventListener('pointerup', e => {
    if (!down) return;
    const moved = Math.hypot(e.clientX - down.x, e.clientY - down.y);
    down = null;
    if (moved > 5) return;
    const id = pickAt(e.clientX, e.clientY);
    if (id) { selectStar(id); flyToNode(id); }
    else if (state.selectedId) selectStar(null);
  });
  el.addEventListener('pointermove', e => {
    if (down) return;
    pending = e;
    if (queued) return;
    queued = true;
    requestAnimationFrame(() => {
      queued = false;
      const ev = pending;
      if (!ev || !gx.starGeo) return;
      const id = pickAt(ev.clientX, ev.clientY);
      if (id !== gx.hoverId) {
        gx.hoverId = id;
        updateMarkers();
        gx.labelsDirty = true;
      }
      stage.classList.toggle('hovering', !!id);
      if (id) {
        tooltipEl.innerHTML = tooltipHtml(state.nodeMap.get(id));
        tooltipEl.classList.add('show');
        tooltipEl.style.left = (ev.pageX + 14) + 'px';
        tooltipEl.style.top = (ev.pageY + 14) + 'px';
      } else tooltipEl.classList.remove('show');
    });
  });
  el.addEventListener('pointerleave', () => {
    gx.hoverId = null;
    updateMarkers();
    tooltipEl.classList.remove('show');
  });

  gx.ro = new ResizeObserver(() => {
    const w = stage.clientWidth, h = stage.clientHeight;
    if (!w || !h) return;
    gx.renderer.setSize(w, h);
    gx.camera.aspect = w / h;
    gx.camera.updateProjectionMatrix();
  });
  gx.ro.observe(stage);
}

function onKey(e) {
  if (e.key === 'Escape' && document.activeElement?.tagName !== 'INPUT') {
    selectStar(null);
  }
}

// ─── SELECCIÓN + SIDEBAR ─────────────────────────────────
function selectStar(id) {
  state.selectedId = id;
  renderNodeInfoG();
  applyHighlights();
}
function jump(id) {
  if (id === SELF_KEY && !state.nodeMap.has(id)) { selectStar(null); flyTo([0, 0, 0], 260); return; }
  selectStar(id); flyToNode(id);
}

function renderNodeInfoG() {
  const box = document.getElementById('nodeInfo');
  if (!state.selectedId) {
    box.innerHTML = '<div class="node-info-empty">click any star in the galaxy</div>';
    return;
  }
  const d = state.nodeMap.get(state.selectedId);
  if (!d) { box.innerHTML = '<div class="node-info-empty">node not found</div>'; return; }

  const ins = Array.from(state.inAdj.get(d.id) || []);
  const outs = Array.from(state.outAdj.get(d.id) || []);
  const fins = Array.from(state.followIn.get(d.id) || []);
  const fouts = Array.from(state.followOut.get(d.id) || []);
  const net = state.netOf.get(d.id);
  const t = gx.time.get(d.id);

  let html = `<div class="node-info-name">${escapeHtml(d.id)}</div><dl>`;
  if (d.id === SELF_ID) html += `<dt>órbita</dt><dd class="accent">eres tú · el sol</dd>`;
  else if (t?.age != null) {
    html += `<dt>órbita</dt><dd class="accent">hace ${fmtAge(t.age)}</dd>`;
    html += `<dt>fecha</dt><dd>${new Date(t.t).toISOString().slice(0, 10)} <span class="time-chip">${t.src}</span></dd>`;
  } else html += `<dt>órbita</dt><dd class="pink">sin fecha · banda exterior</dd>`;

  const tie = selfTie(d);
  if (d.id !== SELF_KEY) html += `<dt>contigo</dt><dd class="${tie === 'mutual' ? 'accent' : tie ? '' : 'pink'}">${tie === 'mutual' ? '⇅ mutual' : tie === 'sigues' ? 'lo sigues' : tie === 'te sigue' ? 'te sigue' : 'sin lazo directo'}</dd>`;
  if (state.deadSet.has(d.id)) html += `<dt>family</dt><dd style="color:${DEAD_COLOR};">dead branch</dd>`;
  if (net) {
    html += `<dt>brazo</dt><dd><span class="tier-badge tier-${net.tier}" data-net="${net.id}">${TIER[net.tier].label}</span> @${escapeHtml(net.name)}</dd>`;
    if (net.hubs.includes(d.id)) html += `<dt>rol</dt><dd class="accent">hub de su red</dd>`;
  }

  if (d.kind === 'tracked') {
    html += `<dt>status</dt><dd class="${d.status === 'active' ? 'accent' : ''}">${escapeHtml(d.status || '—')}</dd>`;
    html += `<dt>mutual</dt><dd class="${d.mutual ? 'accent' : ''}">${d.mutual ? 'yes' : 'no'}</dd>`;
    html += `<dt>origen</dt><dd class="pink">${escapeHtml(d.origen || '—')}</dd>`;
    if (d.request_state) html += `<dt>request</dt><dd>${escapeHtml(d.request_state)}</dd>`;
    if (d.is_private != null) html += `<dt>cuenta</dt><dd>${d.is_private ? 'privada' : 'pública'}</dd>`;
    if (d.followed_at) html += `<dt>followed</dt><dd>${d.followed_at.slice(0, 10)}</dd>`;
    if (d.unfollowed_at) html += `<dt>unfollowed</dt><dd class="pink">${d.unfollowed_at.slice(0, 10)}</dd>`;
    if (d.last_updated) html += `<dt>updated</dt><dd>${d.last_updated.slice(0, 10)}</dd>`;
    if (d.profile_followers !== '') html += `<dt>followers</dt><dd>${d.profile_followers}</dd>`;
    if (d.profile_following !== '') html += `<dt>following</dt><dd>${d.profile_following}</dd>`;
    if (d.profile_ratio !== '') html += `<dt>ratio</dt><dd>${d.profile_ratio}</dd>`;
    if (d.stand_type) html += `<dt>type</dt><dd>${escapeHtml(d.stand_type)}</dd>`;
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
    el.addEventListener('click', () => jump(el.getAttribute('data-jump')));
  });
  box.querySelectorAll('[data-net]').forEach(el => {
    el.addEventListener('click', () => toggleFocusNet(Number(el.getAttribute('data-net'))));
  });
}

function netAgeRange(net) {
  const ages = net.members.map(id => gx.time.get(id)).filter(r => r && r.age != null && !r.inferred).map(r => r.age).sort((a, b) => a - b);
  if (!ages.length) return null;
  const q = p => ages[Math.min(ages.length - 1, Math.floor(p * ages.length))];
  return [q(0.1), q(0.9)];
}

function toggleFocusNet(id) {
  state.focusNet = state.focusNet === id ? null : id;
  if (state.focusNet != null) flyToMembers(state.nets[id].members);
  renderNetworksG();
  applyHighlights();
}

function renderNetworksG() {
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
    const hubs = net.hubs.map(h => `<span class="neighbor-chip" data-jump="${escapeHtml(h)}">@${escapeHtml(h)}</span>`).join('');
    const rng = netAgeRange(net);
    const epoch = rng ? ` · ☉ hace ${fmtAge(rng[0])}–${fmtAge(rng[1])}` : '';
    return `<div class="net-item tier-${net.tier}${state.focusNet === net.id ? ' focus' : ''}" data-net="${net.id}">
      <div class="net-head">
        <span class="net-name">@${escapeHtml(net.name)}</span>
        <span class="tier-badge tier-${net.tier}">${TIER[net.tier].label}</span>
      </div>
      <div class="net-meta">${net.size} nodos · ${net.mutuals} mutual · ${net.yours} sigues · ${net.seen} vistos${net.followsYou ? ` · ${net.followsYou} te siguen` : ''}${net.avgScore != null ? ` · score ⌀${net.avgScore.toFixed(1)}` : ''}${epoch}</div>
      <div class="net-bar"><div class="net-bar-fill" style="width:${pct}%"></div><span>${pct}%</span></div>
      <div class="net-hubs">${hubs}</div>
    </div>`;
  }).join('');

  list.querySelectorAll('.net-item').forEach(el => {
    el.addEventListener('click', () => toggleFocusNet(Number(el.getAttribute('data-net'))));
  });
  list.querySelectorAll('[data-jump]').forEach(el => {
    el.addEventListener('click', (e) => { e.stopPropagation(); jump(el.getAttribute('data-jump')); });
  });
}

function runSearchG() {
  const q = document.getElementById('searchInput').value.toLowerCase().trim();
  const box = document.getElementById('searchResults');
  if (!q) { box.innerHTML = ''; applyHighlights(); return; }

  const matches = state.nodes
    .filter(n => n.id.toLowerCase().includes(q) && matchesFilter(n))
    .slice(0, 50);

  box.innerHTML = matches.map(n => {
    const tag = n.id === SELF_ID ? 'sol'
      : state.deadSet.has(n.id) ? 'dead'
      : n.ghost ? 'origin'
      : n.mutual ? 'mutual'
      : n.kind === 'tracked' ? (n.status || '—') : n.kind;
    const age = gx.time.get(n.id)?.age;
    return `<div class="search-result" data-id="${escapeHtml(n.id)}">
      <span>@${escapeHtml(n.id)}</span><span class="badge">${tag}${age != null ? ' · ' + fmtAge(age) : ''}</span>
    </div>`;
  }).join('');
  box.querySelectorAll('.search-result').forEach(el => {
    el.addEventListener('click', () => jump(el.getAttribute('data-id')));
  });
  applyHighlights();
}

function tracePathG() {
  const fromId = resolvePathInput(document.getElementById('pathFrom').value);
  const toId = resolvePathInput(document.getElementById('pathTo').value);
  const out = document.getElementById('pathResult');

  if (!fromId || !toId) {
    out.innerHTML = '<div class="path-empty">enter two usernames to find connection</div>';
    return;
  }
  if (!pathNodeExists(fromId)) { out.innerHTML = `<div class="path-fail">@${escapeHtml(fromId)} not in graph</div>`; return; }
  if (!pathNodeExists(toId)) { out.innerHTML = `<div class="path-fail">@${escapeHtml(toId)} not in graph</div>`; return; }

  // con "pasar por ti": dos mutuals tuyos quedan a 2 saltos (A → tú → B)
  const path = shortestPath(pathAdjacency(state.pathViaSelf), fromId, toId);
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
    const age = gx.time.get(id)?.age;
    html += `<div class="path-step" data-id="${escapeHtml(id)}">
      <span class="num">${String(i + 1).padStart(2, '0')}</span><span>${escapeHtml(pathName(id))}</span>${age != null ? `<span class="time-chip">${fmtAge(age)}</span>` : ''}
    </div>`;
    if (i < path.length - 1) html += `<div class="path-arrow">${pathRelationLabel(path[i], path[i + 1])}</div>`;
  });
  out.innerHTML = html;
  out.querySelectorAll('.path-step').forEach(el => {
    el.addEventListener('click', () => jump(el.getAttribute('data-id')));
  });
  flyToMembers(path);
  applyHighlights();
}

function clearPathG() {
  document.getElementById('pathFrom').value = '';
  document.getElementById('pathTo').value = '';
  state.pathIds = new Set();
  state.pathOrdered = [];
  document.getElementById('pathResult').innerHTML = '<div class="path-empty">enter two usernames to find connection</div>';
  applyHighlights();
}

function renderStatsG() {
  const set = (id, v) => { const el = document.getElementById(id); if (el) el.textContent = v; };
  const real = state.nodes.filter(n => n.id !== SELF_ID);
  const nFollows = state.links.filter(l => l.types.has('follows')).length;
  const nOrigen = state.links.filter(l => l.types.has('origen')).length;
  set('statNodes', real.length);
  set('statEdges', state.links.length);
  set('statEdgesSub', `${nFollows} follows · ${nOrigen} origen`);
  set('statMutuals', real.filter(n => n.mutual).length);
  set('statArms', gx.arms.length);
  set('statArmsSub', `${state.nets.length} redes ≥ 3`);
  set('statInfiltrated', state.nets.filter(n => n.tier === 'infiltrated').length);

  const direct = [];
  let undated = 0, inferred = 0, oldest = null;
  real.forEach(n => {
    const r = gx.time.get(n.id);
    if (!r || r.age == null) { undated++; return; }
    if (r.inferred) { inferred++; return; }
    direct.push(r.age);
    if (!oldest || r.age > oldest.age) oldest = { id: n.id, age: r.age };
  });
  direct.sort((a, b) => a - b);
  set('statMedian', direct.length ? fmtAge(direct[direct.length >> 1]) : '—');
  set('statOldest', oldest ? fmtAge(oldest.age) : '—');
  set('statOldestSub', oldest ? '@' + oldest.id : '');
  set('statUndated', undated);
  set('statUndatedSub', `${inferred} con fecha inferida`);
}

// ─── TOOLBAR ─────────────────────────────────────────────
function setScale(scale) {
  if (scale === gx.scale && !gx.anim) return;
  gx.scale = scale;
  const to = computeLayout(scale);
  gx.anim = { t0: performance.now(), dur: 1100, from: gx.pos.slice(), to };
  buildRings();
}

function setShape(shape) {
  if (shape === gx.shape) return;
  gx.shape = shape;
  const to = computeLayout(gx.scale);
  gx.anim = { t0: performance.now(), dur: 1300, from: gx.pos.slice(), to };
  gx.disc.visible = shape === 'disc';
  gx.ringGroup.quaternion.identity();
  buildRings();
  resetView();
}

function wireUI() {
  const searchInput = document.getElementById('searchInput');
  searchInput.oninput = runSearchG;

  document.querySelectorAll('.chip').forEach(c => {
    c.onclick = () => {
      document.querySelectorAll('.chip').forEach(x => x.classList.remove('active'));
      c.classList.add('active');
      state.filter = c.getAttribute('data-filter');
      runSearchG();
    };
    c.classList.toggle('active', c.getAttribute('data-filter') === state.filter);
  });

  const pathFrom = document.getElementById('pathFrom');
  const pathTo = document.getElementById('pathTo');
  document.getElementById('pathBtn').onclick = tracePathG;
  document.getElementById('pathClearBtn').onclick = clearPathG;
  pathFrom.onkeydown = (e) => { if (e.key === 'Enter') tracePathG(); };
  pathTo.onkeydown = (e) => { if (e.key === 'Enter') tracePathG(); };

  document.getElementById('resetBtn').onclick = () => {
    state.focusNet = null;
    renderNetworksG();
    selectStar(null);
    resetView();
  };

  const btn = (id, isOn, onClick) => {
    const b = document.getElementById(id);
    if (!b) return;
    b.classList.toggle('active', isOn());
    b.onclick = () => { onClick(b); b.classList.toggle('active', isOn()); };
  };
  btn('rotateBtn', () => gx.autoRotate, () => { gx.autoRotate = !gx.autoRotate; gx.controls.autoRotate = gx.autoRotate; });
  btn('labelsBtn', () => state.showLabels, () => { state.showLabels = !state.showLabels; gx.labelsDirty = true; });
  btn('followsBtn', () => state.showFollows, () => { state.showFollows = !state.showFollows; styleLines(); updateHlLines(); });
  btn('origenBtn', () => state.showOrigen, () => { state.showOrigen = !state.showOrigen; styleLines(); });
  btn('ringsBtn', () => gx.showRings, () => { gx.showRings = !gx.showRings; gx.ringGroup.visible = gx.showRings; gx.labelsDirty = true; });

  const RAY_NEXT = { all: 'yours', yours: 'off', off: 'all' };
  const RAY_TXT = { all: 'RAYOS: TODOS', yours: 'RAYOS: SIGUES', off: 'RAYOS: OFF' };
  const raysBtn = document.getElementById('raysBtn');
  raysBtn.textContent = RAY_TXT[gx.rays];
  btn('raysBtn', () => gx.rays !== 'off', (b) => {
    gx.rays = RAY_NEXT[gx.rays];
    b.textContent = RAY_TXT[gx.rays];
    rebuildRayIdx();
    writeLinePositions();
    styleLines();
  });

  const scaleBtn = document.getElementById('scaleBtn');
  scaleBtn.textContent = gx.scale === 'log' ? 'ESCALA: LOG' : 'ESCALA: LINEAL';
  scaleBtn.onclick = () => {
    setScale(gx.scale === 'log' ? 'linear' : 'log');
    scaleBtn.textContent = gx.scale === 'log' ? 'ESCALA: LOG' : 'ESCALA: LINEAL';
  };

  const shapeBtn = document.getElementById('shapeBtn');
  if (shapeBtn) {
    const txt = () => { shapeBtn.textContent = gx.shape === 'disc' ? 'FORMA: DISCO' : 'FORMA: ESFERA'; };
    txt();
    shapeBtn.onclick = () => { setShape(gx.shape === 'disc' ? 'sphere' : 'disc'); txt(); };
  }

  const via = document.getElementById('pathViaSelf');
  if (via) {
    via.checked = state.pathViaSelf !== false;
    via.onchange = () => { state.pathViaSelf = via.checked; if (state.pathOrdered.length) tracePathG(); };
  }

  const colorBtn = document.getElementById('colorBtn');
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
    styleStars();
  };

  const legend = document.getElementById('galaxyLegend');
  const legendToggle = document.getElementById('legendToggle');
  if (legend && legendToggle) {
    const KEY = 'polpo.galaxy.legend';
    const setC = c => {
      legend.classList.toggle('collapsed', c);
      legendToggle.querySelector('span').textContent = c ? '+' : '−';
      try { localStorage.setItem(KEY, c ? '1' : '0'); } catch (e) { /* sin storage */ }
    };
    let c0 = false;
    try { c0 = localStorage.getItem(KEY) === '1'; } catch (e) { /* sin storage */ }
    setC(c0);
    legendToggle.onclick = () => setC(!legend.classList.contains('collapsed'));
  }

  window.addEventListener('keydown', onKey);
}

// ─── ENTRY POINT ─────────────────────────────────────────
// misma firma que dashboard.js → app.js no cambia
function buildGalaxy(rows, extras = {}) {
  const { nodes, links } = buildGraph(rows, extras.followedBy, extras.red);
  if (!nodes.length) { showToast('no nodes in result'); return; }

  state.nodes = nodes;
  state.links = links;
  state.hasFollowData = (extras.followedBy || []).length > 0;
  Object.assign(state, indexGraph(nodes, links));
  state.deadSet = computeDeadFamilies();
  const { nets, netOf, bodies, groupOf } = computeNetworks();
  Object.assign(state, { nets, netOf, bodies, groupOf });
  state.roles = computeRoles();
  Object.assign(state, {
    focusNet: null, selectedId: null, pathIds: new Set(), pathOrdered: [],
    filter: 'all', showOrigen: false, showFollows: true, showLabels: true,
  });

  // orden de buffers + seeds deterministas
  gx.order = nodes;
  gx.idx = new Map(nodes.map((n, i) => [n.id, i]));
  gx.seeds = nodes.map(n => {
    const rnd = mulberry32(hashStr(n.id));
    return { ga: gauss(rnd), gy: gauss(rnd), u: rnd(), u2: rnd(), gb: gauss(rnd), u3: rnd() };
  });

  computeTimes();
  computeArms();
  gx.pos = computeLayout(gx.scale);

  initScene();
  buildStars();
  buildLines();
  buildRings();
  writeStarPositions();
  wireCanvas();
  wireUI();

  renderStatsG();
  renderNetworksG();
  renderNodeInfoG();
  runSearchG();
  applyHighlights();
  animate();

  if (SELF_ID && !state.nodeMap.has(SELF_ID)) {
    console.info(`galaxy: SELF_USERNAME @${SELF_ID} no aparece en los datos; el sol queda sin nodo propio`);
  }
}

function destroyGalaxy() {
  cancelAnimationFrame(gx.raf);
  gx.ro?.disconnect();
  window.removeEventListener('keydown', onKey);
  if (gx.scene) {
    gx.scene.traverse(o => {
      o.geometry?.dispose();
      if (o.material) { o.material.map?.dispose(); o.material.dispose(); }
    });
  }
  gx.renderer?.dispose();
  const stage = document.getElementById('galaxyStage');
  if (stage) stage.innerHTML = '';
  const lb = document.getElementById('galaxyLabels');
  if (lb) lb.innerHTML = '';
  Object.assign(gx, {
    labelPool: [], labelItems: [], anim: null, fly: null, hoverId: null, alpha: null,
    renderer: null, scene: null, stars: null, starGeo: null, followLines: null,
    origenLines: null, rayLines: null, hlLines: null, ringGroup: null, marker: null, hoverMarker: null,
  });
  Object.assign(state, {
    nodes: [], links: [],
    adj: new Map(), outAdj: new Map(), inAdj: new Map(),
    followOut: new Map(), followIn: new Map(), nodeMap: new Map(),
    deadSet: new Set(), nets: [], netOf: new Map(), focusNet: null,
    groupOf: new Map(), bodies: [], roles: new Map(),
    selectedId: null, pathIds: new Set(), pathOrdered: [],
  });
}

window.POLPO_DASHBOARD = { buildDashboard: buildGalaxy, destroyDashboard: destroyGalaxy, showToast, _state: state, _gx: gx };

// ─── DEMO (?demo) ────────────────────────────────────────
// datos inventados para ver la galaxia sin Supabase
function makeDemoData() {
  const rnd = mulberry32(1337);
  const now = Date.now();
  const iso = days => new Date(now - Math.max(0, days) * DAY).toISOString();
  const pick = arr => arr[Math.floor(rnd() * arr.length)];
  const A = ['luna', 'nico', 'vale', 'mau', 'sofi', 'dani', 'fer', 'ale', 'pau', 'santi', 'regi', 'emi', 'xime', 'rodri', 'cami', 'leo', 'majo', 'beto', 'ana', 'pepe', 'kari', 'iker', 'nat', 'ollin'];
  const B = ['', '.', '_', '__', '.x', '_mx', '.cdmx', '_ok', '.art', '.foto', '_skt', '.lol'];
  const used = new Set();
  const uname = () => {
    for (;;) {
      const u = pick(A) + pick(B) + (rnd() < 0.6 ? Math.floor(rnd() * 99) : '');
      if (!used.has(u)) { used.add(u); return u; }
    }
  };

  const clusters = [
    { age: 3, w: 3, n: 40, mut: 0.25, unf: 0.0 },
    { age: 18, w: 8, n: 70, mut: 0.35, unf: 0.1 },
    { age: 45, w: 15, n: 55, mut: 0.2, unf: 0.25 },
    { age: 95, w: 25, n: 80, mut: 0.3, unf: 0.35 },
    { age: 160, w: 30, n: 45, mut: 0.05, unf: 0.6 },
    { age: 260, w: 45, n: 60, mut: 0.15, unf: 0.55 },
    { age: 420, w: 60, n: 50, mut: 0.02, unf: 0.95 },
    { age: 610, w: 70, n: 35, mut: 0.1, unf: 0.8 },
    { age: 30, w: 25, n: 25, mut: 0.0, unf: 0.3 },
  ];
  const rows = [], fb = [], red = [];
  clusters.forEach(cl => {
    const origins = [uname(), uname()];
    const ext = Array.from({ length: 3 + Math.floor(rnd() * 4) }, uname);
    const members = [];
    for (let k = 0; k < cl.n; k++) {
      const u = uname();
      const age = cl.age + gauss(rnd) * cl.w;
      const mutual = rnd() < cl.mut;
      const unf = !mutual && rnd() < cl.unf;
      rows.push({
        username: u,
        status: unf ? 'unfollowed' : 'active',
        mutual,
        origen: pick(origins),
        followed_at: iso(age),
        mutual_checked_at: iso(age - 2),
        unfollowed_at: unf ? iso(Math.max(0, age - 3 - rnd() * 20)) : null,
        last_updated: iso(Math.max(0, age - 5)),
        profile_followers: Math.floor(200 + rnd() * 3000),
        profile_following: Math.floor(200 + rnd() * 2000),
        profile_ratio: (0.4 + rnd()).toFixed(4),
        stand_type: pick(['personal', 'creator', 'business']),
      });
      members.push(u);
    }
    const seen = Array.from({ length: Math.floor(cl.n * 0.3) }, uname);
    seen.forEach(s => red.push({ username: s, score: Math.round(rnd() * 100) / 10, total_conns: 2 + Math.floor(rnd() * 8), mutual_conns: Math.floor(rnd() * 3), others: Math.floor(rnd() * 20), follows_you: rnd() < 0.15, checked_at: iso(cl.age + gauss(rnd) * cl.w * 0.5) }));
    const followers = ext.concat(members.filter(() => rnd() < 0.25));
    members.concat(seen).forEach(t => {
      const k = 1 + Math.floor(rnd() * 3);
      for (let j = 0; j < k; j++) fb.push({ username: t, connection: pick(followers) });
    });
    cl.members = members;
  });
  // puentes entre redes
  for (let k = 0; k < 40; k++) {
    const a = pick(clusters), b = pick(clusters);
    fb.push({ username: pick(a.members), connection: pick(b.members) });
  }
  // sueltos (sin red)
  for (let k = 0; k < 60; k++) {
    rows.push({ username: uname(), status: rnd() < 0.5 ? 'unfollowed' : 'active', mutual: rnd() < 0.1, origen: 'unknown', followed_at: iso(rnd() * 700), last_updated: iso(1) });
  }
  return { rows, followedBy: fb, red };
}

window.POLPO_GALAXY_DEMO = function () {
  document.getElementById('loginScreen').classList.add('hidden');
  document.getElementById('loadingScreen').classList.add('hidden');
  document.getElementById('app').classList.remove('hidden');
  document.getElementById('metaUser').textContent = 'demo · datos inventados';
  const go = () => {
    const { rows, followedBy, red } = makeDemoData();
    destroyGalaxy();
    buildGalaxy(rows.map(r => ({ ...r, mutual: r.mutual === true })), { followedBy, red });
  };
  document.getElementById('reloadBtn').onclick = go;
  document.getElementById('logoutBtn').onclick = () => { location.href = location.pathname; };
  requestAnimationFrame(go);
};

})();

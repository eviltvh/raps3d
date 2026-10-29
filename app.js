/* ═══════════════════════════════════════════════════════════
   POLPO :: NETWORK ANALYZER  ·  app.js
   Auth (Supabase) + fetch paginado de stand_users, followed_by
   y red_perfil (estas dos son opcionales: si no existen o RLS no
   deja leerlas, el grafo se arma solo con el linaje de origen).
   No conoce nada del grafo: solo trae rows y se los pasa
   a window.POLPO_DASHBOARD.buildDashboard().
   -bynd
   ═══════════════════════════════════════════════════════════ */

"use strict";

// ─── CONFIG / CLIENT ─────────────────────────────────────
const CFG = window.POLPO_NETWORK_CONFIG || {};
const CFG_INVALID =
  !CFG.SUPABASE_URL ||
  !CFG.SUPABASE_ANON_KEY ||
  CFG.SUPABASE_URL.includes('TU-PROYECTO') ||
  CFG.SUPABASE_ANON_KEY.includes('PEGA_TU_ANON_KEY');

let sb = null;
if (!CFG_INVALID) {
  sb = supabase.createClient(CFG.SUPABASE_URL, CFG.SUPABASE_ANON_KEY, {
    auth: { persistSession: true, autoRefreshToken: true }
  });
}

// ─── DOM REFS ────────────────────────────────────────────
const $loginScreen   = document.getElementById('loginScreen');
const $loadingScreen = document.getElementById('loadingScreen');
const $loadingText   = document.getElementById('loadingText');
const $app           = document.getElementById('app');
const $loginEmail    = document.getElementById('loginEmail');
const $loginPass     = document.getElementById('loginPass');
const $loginBtn      = document.getElementById('loginBtn');
const $loginError    = document.getElementById('loginError');
const $metaUser      = document.getElementById('metaUser');
const $reloadBtn     = document.getElementById('reloadBtn');
const $logoutBtn     = document.getElementById('logoutBtn');

// ─── UI STATE TRANSITIONS ────────────────────────────────
function showLogin() {
  $loginScreen.classList.remove('hidden');
  $loadingScreen.classList.add('hidden');
  $app.classList.add('hidden');
}
function showLoading(text = 'fetching network...') {
  $loginScreen.classList.add('hidden');
  $app.classList.add('hidden');
  $loadingText.textContent = text;
  $loadingScreen.classList.remove('hidden');
}
function showApp(email) {
  $loginScreen.classList.add('hidden');
  $loadingScreen.classList.add('hidden');
  $app.classList.remove('hidden');
  $metaUser.textContent = email || 'authed';
}
function showLoginError(msg) {
  $loginError.textContent = msg;
  $loginError.classList.add('show');
}
function clearLoginError() {
  $loginError.textContent = '';
  $loginError.classList.remove('show');
}

// ─── AUTH ────────────────────────────────────────────────
async function checkSession() {
  if (CFG_INVALID) {
    showLogin();
    showLoginError('config.js no válido. Edita SUPABASE_URL y SUPABASE_ANON_KEY.');
    $loginBtn.disabled = true;
    return;
  }
  try {
    const { data: { session } } = await sb.auth.getSession();
    if (session) {
      showApp(session.user.email);
      await loadFromDB();
    } else {
      showLogin();
    }
  } catch (err) {
    console.error('checkSession error:', err);
    showLogin();
    showLoginError(err.message || 'session check failed');
  }
}

async function doLogin() {
  clearLoginError();
  const email = $loginEmail.value.trim();
  const password = $loginPass.value;
  if (!email || !password) {
    showLoginError('email y password requeridos');
    return;
  }
  $loginBtn.disabled = true;
  $loginBtn.textContent = 'SIGNING IN...';
  try {
    const { data, error } = await sb.auth.signInWithPassword({ email, password });
    if (error) {
      showLoginError(error.message);
      return;
    }
    showApp(data.user.email);
    await loadFromDB();
  } catch (err) {
    console.error('login error:', err);
    showLoginError(err.message || 'login failed');
  } finally {
    $loginBtn.disabled = false;
    $loginBtn.textContent = 'SIGN IN';
  }
}

async function doLogout() {
  try {
    await sb.auth.signOut();
  } catch (err) {
    console.error('logout error:', err);
  }
  window.POLPO_DASHBOARD?.destroyDashboard();
  $loginEmail.value = '';
  $loginPass.value = '';
  showLogin();
}

// ─── PAGINATED FETCH ─────────────────────────────────────
async function fetchAll(tableName, columns, label = 'network') {
  const PAGE = 1000;
  const MAX_PAGES = 50;
  let all = [];
  let from = 0;
  let pages = 0;

  while (pages < MAX_PAGES) {
    $loadingText.textContent = `fetching ${label}... ${all.length} rows`;
    const { data, error } = await sb
      .from(tableName)
      .select(columns)
      .range(from, from + PAGE - 1);
    if (error) throw error;
    if (!data?.length) break;
    all = all.concat(data);
    if (data.length < PAGE) break;
    from += PAGE;
    pages++;
  }
  return all;
}

// ey tablas opcionales: si no existen (migracion sin correr) no truena -bynd
async function fetchOptional(tableName, columns, label) {
  if (!tableName) return { rows: [], missing: true };
  try {
    return { rows: await fetchAll(tableName, columns, label), missing: false };
  } catch (err) {
    const msg = String(err?.message || '');
    const missing = err?.code === '42P01' || err?.code === 'PGRST205' ||
                    /does not exist|could not find|schema cache/i.test(msg);
    console.warn(`fetchOptional(${tableName})`, err);
    return { rows: [], missing, error: missing ? null : msg };
  }
}

// ─── ROW TRANSFORM ───────────────────────────────────────
// Supabase devuelve NUMERIC como string → coerce a number donde aplique.
// El grafo en dashboard.js es tolerante, pero igual lo limpiamos.
function transformRow(row) {
  return {
    username: row.username,
    status: row.status,
    mutual: row.mutual === true,
    origen: row.origen,
    followed_at: row.followed_at,
    mutual_checked_at: row.mutual_checked_at,
    unfollowed_at: row.unfollowed_at,
    last_updated: row.last_updated,
    profile_followers: row.profile_followers != null ? Number(row.profile_followers) : '',
    profile_following: row.profile_following != null ? Number(row.profile_following) : '',
    profile_ratio:     row.profile_ratio     != null ? parseFloat(row.profile_ratio).toFixed(4) : '',
    stand_type: row.stand_type,
    request_state: row.request_state,
    is_private: row.is_private,
  };
}

function transformRed(row) {
  return {
    username: row.username,
    score: row.score != null ? Number(row.score) : null,
    total_conns: Number(row.total_conns || 0),
    mutual_conns: Number(row.mutual_conns || 0),
    others: Number(row.others || 0),
    follows_you: row.follows_you === true,
    checked_at: row.checked_at,
  };
}

// ─── LOAD FROM DB ────────────────────────────────────────
async function loadFromDB() {
  showLoading('fetching network...');
  try {
    // chintrolas request_state/is_private son opcionales (columnas nuevas) -bynd
    let rows;
    try {
      rows = await fetchAll(CFG.TABLE, CFG.COLUMNS + (CFG.EXTRA_COLUMNS ? ',' + CFG.EXTRA_COLUMNS : ''));
    } catch (err) {
      if (!CFG.EXTRA_COLUMNS || !/column/i.test(err?.message || '')) throw err;
      console.warn('columnas nuevas de stand_users aun no existen, sigo sin ellas', err);
      rows = await fetchAll(CFG.TABLE, CFG.COLUMNS);
    }
    if (!rows.length) {
      showApp(); // mostrar shell vacío
      window.POLPO_DASHBOARD?.showToast?.('no rows in stand_users');
      return;
    }

    const [fb, red] = await Promise.all([
      fetchOptional(CFG.TABLE_FOLLOWED_BY, 'username,connection', 'followed_by'),
      fetchOptional(CFG.TABLE_RED, 'username,score,total_conns,mutual_conns,others,follows_you,checked_at', 'red_perfil'),
    ]);

    showApp((await sb.auth.getUser()).data.user?.email);
    window.POLPO_DASHBOARD.destroyDashboard();
    window.POLPO_DASHBOARD.buildDashboard(rows.map(transformRow), {
      followedBy: fb.rows,
      red: red.rows.map(transformRed),
    });

    // aaa avisar por q no hay redes, si es el caso -bynd
    const avisos = [];
    if (fb.missing) avisos.push('followed_by no existe (corre la migración)');
    else if (fb.error) avisos.push(`followed_by: ${fb.error}`);
    else if (!fb.rows.length) avisos.push('followed_by vacío (¿sin datos aún o falta policy RLS de select?)');
    if (red.missing) avisos.push('red_perfil no existe');
    if (avisos.length) window.POLPO_DASHBOARD.showToast(avisos.join(' · '));
  } catch (err) {
    console.error('loadFromDB error:', err);
    showApp();
    window.POLPO_DASHBOARD?.showToast?.(
      `Error: ${err.message} · ¿Activaste RLS y las policies?`
    );
  }
}

// ─── BOOT + LISTENERS ────────────────────────────────────
$loginBtn.addEventListener('click', doLogin);
$loginPass.addEventListener('keydown', e => { if (e.key === 'Enter') doLogin(); });
$loginEmail.addEventListener('keydown', e => { if (e.key === 'Enter') doLogin(); });
$logoutBtn.addEventListener('click', doLogout);
$reloadBtn.addEventListener('click', loadFromDB);

sb?.auth.onAuthStateChange((event) => {
  if (event === 'SIGNED_OUT') {
    window.POLPO_DASHBOARD?.destroyDashboard();
    showLogin();
  }
});

checkSession();



window.POLPO_NETWORK_CONFIG = {
  SUPABASE_URL: 'https://jlgudpcsgbzqiryuoxam.supabase.co',
  SUPABASE_ANON_KEY: 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6ImpsZ3VkcGNzZ2J6cWlyeXVveGFtIiwicm9sZSI6ImFub24iLCJpYXQiOjE3Nzc4MjQ3NzQsImV4cCI6MjA5MzQwMDc3NH0.64Ox8kprffYrVaRvyDP95uV8f3mO2wzcmxJxh257_MM',

  // Tabla a leer
  TABLE: 'stand_users',

  // Columnas que necesita el grafo (mantén el orden si quieres)
  COLUMNS: 'username,status,mutual,origen,followed_at,mutual_checked_at,profile_followers,profile_following,profile_ratio,stand_type,unfollowed_at,last_updated',

  // ey columnas de la migracion v3.1 (si aun no existen se ignoran) -bynd
  EXTRA_COLUMNS: 'request_state,is_private',

  // aaa tablas de red (opcionales: sin ellas el grafo es solo linaje de origen) -bynd
  TABLE_FOLLOWED_BY: 'followed_by',
  TABLE_RED: 'red_perfil',

  // galaxy.html: tu username (sin @). Es el sol; si aparece en los datos se funde con él.
  // Vacío = el sol se llama "tú".
  SELF_USERNAME: 'tvh'
};

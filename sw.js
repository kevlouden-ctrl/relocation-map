/**
 * sw.js — Service Worker for Relocation Research Map
 *
 * Strategy:
 *   - App shell (HTML/CSS/JS): cache-first, updated in background
 *   - OSM map tiles: cache-first with network fallback (offline tile viewing)
 *   - Firebase/CDN requests: network-only (never cache auth tokens)
 */

const APP_VERSION  = 'v3';
const APP_CACHE    = `relo-app-${APP_VERSION}`;
const TILE_CACHE   = `relo-tiles-${APP_VERSION}`;
const TILE_MAX_AGE = 7 * 24 * 60 * 60 * 1000; // 7 days in ms

const APP_SHELL = [
  '/',
  '/index.html',
  '/style.css',
  '/app.js',
  '/manifest.json',
  '/icons/icon-192.png',
  '/icons/icon-512.png',
];

// ── Install: pre-cache app shell ─────────────────────────────
self.addEventListener('install', (e) => {
  e.waitUntil(
    caches.open(APP_CACHE)
      .then((cache) => cache.addAll(APP_SHELL))
      .then(() => self.skipWaiting())
  );
});

// ── Activate: remove old caches ──────────────────────────────
self.addEventListener('activate', (e) => {
  e.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(
        keys
          .filter((k) => k !== APP_CACHE && k !== TILE_CACHE)
          .map((k) => caches.delete(k))
      ))
      .then(() => self.clients.claim())
  );
});

// ── Fetch: route by request type ─────────────────────────────
self.addEventListener('fetch', (e) => {
  const { request } = e;
  const url = new URL(request.url);

  // Skip non-GET and cross-origin Firebase/CDN requests
  if (request.method !== 'GET') return;
  if (url.hostname.includes('gstatic.com'))     return;
  if (url.hostname.includes('googleapis.com'))  return;
  if (url.hostname.includes('firebaseapp.com')) return;
  if (url.hostname.includes('unpkg.com'))       return;
  if (url.hostname.includes('overpass-api.de')) return;  // never cache API responses

  // OSM Street + Terrain tiles — cache-first, max 7 days
  if (url.hostname.endsWith('.tile.openstreetmap.org') ||
      url.hostname.endsWith('.tile.opentopomap.org')) {
    e.respondWith(tileStrategy(request));
    return;
  }

  // Esri satellite tiles — cache-first, max 7 days
  if (url.hostname.includes('arcgisonline.com')) {
    e.respondWith(tileStrategy(request));
    return;
  }

  // App shell — cache-first with background refresh
  e.respondWith(appShellStrategy(request));
});

async function tileStrategy(request) {
  const cache  = await caches.open(TILE_CACHE);
  const cached = await cache.match(request);

  if (cached) {
    const cachedDate = cached.headers.get('sw-cached-date');
    const age = cachedDate ? Date.now() - Number(cachedDate) : Infinity;
    if (age < TILE_MAX_AGE) return cached;
  }

  try {
    const response = await fetch(request);
    if (response.ok) {
      // Clone and stamp with cache date before storing
      const headers  = new Headers(response.headers);
      headers.set('sw-cached-date', String(Date.now()));
      const stamped  = new Response(await response.clone().arrayBuffer(), {
        status:  response.status,
        headers,
      });
      cache.put(request, stamped);
    }
    return response;
  } catch {
    return cached ?? new Response('Tile unavailable offline', { status: 503 });
  }
}

async function appShellStrategy(request) {
  const cache  = await caches.open(APP_CACHE);
  const cached = await cache.match(request);

  // Kick off background refresh
  const networkFetch = fetch(request)
    .then((response) => {
      if (response.ok) cache.put(request, response.clone());
      return response;
    })
    .catch(() => null);

  return cached ?? await networkFetch ?? new Response('Offline', { status: 503 });
}

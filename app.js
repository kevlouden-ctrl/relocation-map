/**
 * app.js — Relocation Research Map
 * Sprint 3: Finger Paint + Polygon drawing tools
 *
 * Firestore collections:
 *   pins     — pin drop markers
 *   drawings — all drawn overlays (single collection), differentiated by `type`:
 *               stroke: { userId, type:'stroke', rating, points:[{lat,lng,r}], createdAt }
 *               area:   { userId, type:'area', rating, note, vertices:[{lat,lng}], createdAt }
 *
 * Update Firestore security rules to cover the new collections (see Firebase console → Rules):
 *
 *   rules_version = '2';
 *   service cloud.firestore {
 *     match /databases/{database}/documents {
 *       match /{col}/{id} {
 *         allow read, delete: if request.auth != null
 *                             && request.auth.uid == resource.data.userId;
 *         allow create: if request.auth != null
 *                       && request.auth.uid == request.resource.data.userId;
 *       }
 *     }
 *   }
 *
 * ⚠️  Serve over HTTP, not file://: python3 -m http.server 8080
 */

// ============================================================
// 1. Firebase Imports — all pinned to 10.14.1
// ============================================================
import { initializeApp } from 'https://www.gstatic.com/firebasejs/10.14.1/firebase-app.js';
import {
  getAuth,
  GoogleAuthProvider,
  signInWithPopup,
  signOut,
  onAuthStateChanged,
} from 'https://www.gstatic.com/firebasejs/10.14.1/firebase-auth.js';
import {
  initializeFirestore,
  collection,
  addDoc,
  deleteDoc,
  updateDoc,
  doc,
  query,
  where,
  getDocs,
  serverTimestamp,
} from 'https://www.gstatic.com/firebasejs/10.14.1/firebase-firestore.js';

// ============================================================
// 2. Firebase Config
// ============================================================
const firebaseConfig = {
  apiKey:            "AIzaSyCfDynmgL7Xbg-3yYXOp5vePwxh2vr_xxo",
  authDomain:        "relocation-map-30570.firebaseapp.com",
  projectId:         "relocation-map-30570",
  storageBucket:     "relocation-map-30570.firebasestorage.app",
  messagingSenderId: "77195598520",
  appId:             "1:77195598520:web:4643e2639206b369c7f24d",
};

// ============================================================
// 3. Firebase init vars — populated in initAuth()
// ============================================================
let auth = null;
let db   = null;

// ============================================================
// 4. Constants
// ============================================================
const PIN_COLORS = { good: '#4CAF50', bad: '#F44336', neutral: '#9E9E9E' };

const BASE_TILE_LAYERS = {
  street: L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
    attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors',
    maxZoom:           19,
    keepBuffer:        4,   // pre-fetch tiles 4 tiles outside viewport (default 2)
  }),
  satellite: L.tileLayer(
    'https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',
    {
      attribution:       '&copy; <a href="https://www.esri.com/">Esri</a>',
      maxZoom:           19,
      keepBuffer:        4,
      updateWhenZooming: false, // scale existing tiles during zoom, fetch crisp tiles after
    }
  ),
  terrain: L.tileLayer('https://{s}.tile.opentopomap.org/{z}/{x}/{y}.png', {
    attribution: '&copy; <a href="https://opentopomap.org">OpenTopoMap</a>',
    maxZoom:           17,
    keepBuffer:        4,
  }),
};

const PAINT_FILL = { good: '#4CAF50', bad: '#F44336', neutral: '#9E9E9E' };
const PAINT_STROKE_OPACITY = 0.35;
const PAINT_RADIUS_PX      = 16;   // visual radius → converted to meters at paint time
const PAINT_MIN_DIST_PX    = 8;    // min px between consecutive paint dots
const PAINT_MAX_POINTS     = 500;  // per-stroke cap (Firestore doc size guard)

// ============================================================
// 5. State
// ============================================================
// — App —
let currentMode = 'none';  // 'none' | 'pin' | 'paint' | 'polygon'
let currentUser = null;
let map         = null;

// — Modal —
let modalContext   = null;  // { type:'pin', latlng } | { type:'polygon', vertices }
let selectedRating = null;

// — Location —
let locationMarker = null;
let accuracyCircle = null;
let watchId        = null;
let followMe       = false;

// — Paint —
let paintRating        = 'neutral';
let isPainting         = false;
let activeStroke       = [];  // { lat, lng, r } — current drag points
let activeStrokeLayers = [];  // L.circle — layers for the current drag
let allStrokes         = [];  // { layers, points, rating, docId } — all strokes (for undo/clear)
let lastPaintPx        = null;
let lastPaintTime      = 0;

// — Polygon —
let polygonVertices      = [];
let polygonVertexMarkers = [];
let polygonPreviewLine   = null;
let polygonRubberBand    = null;

// — Notes panel —
let reviewItems  = [];   // sorted by createdAt desc; populated by loaders + saves
const geocodeCache = {}; // { "lat,lng": "City, State" } — Nominatim cache

// — Layers —
let activeBaseTileLayer = null;
let activeBaseLayerName = 'street';

const overlayGroups = {
  powerLines:   L.layerGroup(),
  substations:  L.layerGroup(),
  powerPlants:  L.layerGroup(),
};
const overlayLoaded  = { powerLines: false, substations: false, powerPlants: false };
const activeOverlays = new Set();
let   powerFetchTimer = null;

// ============================================================
// 5.5 Review helpers
// ============================================================
function computeCentroid(points) {
  const lat = points.reduce((s, p) => s + p.lat, 0) / points.length;
  const lng = points.reduce((s, p) => s + p.lng, 0) / points.length;
  return { lat, lng };
}

function pushReviewItem(item) {
  reviewItems.push(item);
  reviewItems.sort((a, b) => b.createdAt - a.createdAt);
}

function relativeTime(date) {
  const diff = Date.now() - date.getTime();
  const sec  = diff / 1000;
  const min  = sec  / 60;
  const hr   = min  / 60;
  const day  = hr   / 24;
  if (sec < 60)  return 'just now';
  if (min < 60)  return `${Math.floor(min)}m ago`;
  if (hr  < 24)  return `${Math.floor(hr)}h ago`;
  if (day < 7)   return `${Math.floor(day)}d ago`;
  return date.toLocaleDateString();
}

// ============================================================
// 6. initMap
// ============================================================
function initMap() {
  map = L.map('map', {
    center:      [37.0, -80.0],
    zoom:        6,
    zoomControl: false,
    zoomSnap:    0.5,   // fractional zoom levels — removes the harsh integer-step feel
    zoomDelta:   0.5,   // +/- button and keyboard zoom in 0.5-level increments
  });

  // Zoom to bottom-left — clear of toolbar and auth bar
  L.control.zoom({ position: 'bottomleft' }).addTo(map);

  map.on('click', onMapClick);

  map.on('dragstart', () => {
    if (followMe) disableFollowMe();
  });
}

// ============================================================
// 6.5 Layers — base tile switcher + infrastructure overlays
// ============================================================
function initLayers() {
  // Add default base layer to map
  activeBaseTileLayer = BASE_TILE_LAYERS.street;
  activeBaseTileLayer.addTo(map);

  const btnLayers = document.getElementById('btn-layers');
  const panel     = document.getElementById('layers-panel');

  // Toggle panel open/close
  btnLayers.addEventListener('click', (e) => {
    e.stopPropagation();
    const opening = panel.classList.contains('hidden');
    panel.classList.toggle('hidden', !opening);
    btnLayers.classList.toggle('active', opening);
    btnLayers.setAttribute('aria-expanded', String(opening));
  });

  // Close on Escape
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && !panel.classList.contains('hidden')) {
      panel.classList.add('hidden');
      btnLayers.classList.remove('active');
      btnLayers.setAttribute('aria-expanded', 'false');
    }
  });

  // Close on click-outside
  document.addEventListener('click', (e) => {
    if (!panel.classList.contains('hidden') &&
        !panel.contains(e.target) &&
        !btnLayers.contains(e.target)) {
      panel.classList.add('hidden');
      btnLayers.classList.remove('active');
      btnLayers.setAttribute('aria-expanded', 'false');
    }
  });

  // Base layer radio buttons
  document.querySelectorAll('.base-layer-btn').forEach((btn) => {
    btn.addEventListener('click', () => switchBaseLayer(btn.dataset.layer));
  });

  // Overlay toggle buttons
  document.querySelectorAll('.overlay-btn').forEach((btn) => {
    btn.addEventListener('click', () => toggleOverlay(btn.dataset.overlay));
  });

  // Re-fetch viewport-based overlays on map pan/zoom
  map.on('moveend', onLayerMoveEnd);
}

function switchBaseLayer(name) {
  if (name === activeBaseLayerName) return;
  map.removeLayer(activeBaseTileLayer);
  activeBaseTileLayer = BASE_TILE_LAYERS[name];
  activeBaseTileLayer.addTo(map);
  activeBaseLayerName = name;

  document.querySelectorAll('.base-layer-btn').forEach((btn) => {
    btn.classList.toggle('active', btn.dataset.layer === name);
  });
}

function toggleOverlay(key) {
  const btn = document.querySelector(`.overlay-btn[data-overlay="${key}"]`);
  if (activeOverlays.has(key)) {
    activeOverlays.delete(key);
    map.removeLayer(overlayGroups[key]);
    btn.classList.remove('active');
    btn.setAttribute('aria-pressed', 'false');
    // Viewport-based overlays re-fetch fresh data on next toggle-ON.
    // powerPlants is a one-time US-wide load — keep cached across toggles.
    if (key !== 'powerPlants') overlayLoaded[key] = false;
  } else {
    activeOverlays.add(key);
    overlayGroups[key].addTo(map);
    btn.classList.add('active');
    btn.setAttribute('aria-pressed', 'true');
    if (!overlayLoaded[key]) loadOverlay(key);
  }
}

function loadOverlay(key) {
  switch (key) {
    case 'powerLines':  return loadPowerLines();
    case 'substations': return loadSubstations();
    case 'powerPlants': return loadPowerPlants();
  }
}

async function fetchOverpassData(query, timeoutMs = 20000) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    const resp = await fetch('https://overpass-api.de/api/interpreter', {
      method:  'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body:    `data=${encodeURIComponent(query)}`,
      signal:  controller.signal,
    });
    if (!resp.ok) throw new Error(`Overpass error: ${resp.status}`);
    return resp.json();
  } finally {
    clearTimeout(timer);
  }
}

function setOverlayLoading(key, isLoading) {
  const btn = document.querySelector(`.overlay-btn[data-overlay="${key}"]`);
  if (btn) btn.classList.toggle('loading', isLoading);
}

async function loadPowerLines() {
  if (map.getZoom() < 7) {
    overlayGroups.powerLines.clearLayers();
    const center = map.getCenter();
    L.marker(center, {
      icon: L.divIcon({
        html:      '<div class="zoom-notice">Zoom in (level 7+) to see power lines</div>',
        className: '',
        iconSize:  [246, 30],
        iconAnchor:[123, 15],
      }),
      interactive: false,
    }).addTo(overlayGroups.powerLines);
    return;
  }

  overlayLoaded.powerLines = true;
  setOverlayLoading('powerLines', true);
  const b    = map.getBounds();
  const bbox = `${b.getSouth()},${b.getWest()},${b.getNorth()},${b.getEast()}`;
  try {
    const data = await fetchOverpassData(
      `[out:json][timeout:25];way["power"="line"](${bbox});out geom qt;`,
      32000   // client timeout > server timeout so server error reaches us cleanly
    );
    // Swap in new data only after a successful fetch — old lines stay visible while loading
    overlayGroups.powerLines.clearLayers();
    data.elements.forEach((el) => {
      if (!el.geometry?.length) return;
      const coords   = el.geometry.map((p) => [p.lat, p.lon]);
      const voltage  = el.tags?.voltage  ? `<br>Voltage: ${el.tags.voltage} V`          : '';
      const name     = el.tags?.name     ? `<br>${escapeHtml(el.tags.name)}`             : '';
      const operator = el.tags?.operator ? `<br>Op: ${escapeHtml(el.tags.operator)}`    : '';
      L.polyline(coords, { color: '#FF8C00', weight: 4, opacity: 1.0 })
        .bindPopup(`<b>Power Line</b>${voltage}${name}${operator}`, { maxWidth: 220 })
        .addTo(overlayGroups.powerLines);
    });
  } catch (err) {
    console.error('Power lines fetch failed:', err);
    overlayLoaded.powerLines = false;  // allow retry on next toggle
  } finally {
    setOverlayLoading('powerLines', false);
  }
}

async function loadSubstations() {
  if (map.getZoom() < 7) return;

  overlayLoaded.substations = true;
  setOverlayLoading('substations', true);
  const b    = map.getBounds();
  const bbox = `${b.getSouth()},${b.getWest()},${b.getNorth()},${b.getEast()}`;
  try {
    const data = await fetchOverpassData(
      `[out:json][timeout:25];(node["power"="substation"](${bbox});way["power"="substation"](${bbox}););out center qt;`,
      32000
    );
    // Swap in new data only after successful fetch — old markers stay visible while loading
    overlayGroups.substations.clearLayers();
    data.elements.forEach((el) => {
      const lat = el.lat ?? el.center?.lat;
      const lon = el.lon ?? el.center?.lon;
      if (lat == null || lon == null) return;
      const voltage  = el.tags?.voltage  ? `<br>Voltage: ${el.tags.voltage} V`       : '';
      const name     = el.tags?.name     ? `<br>${escapeHtml(el.tags.name)}`          : '';
      const operator = el.tags?.operator ? `<br>Op: ${escapeHtml(el.tags.operator)}` : '';
      L.circleMarker([lat, lon], {
        radius: 9, color: '#fff', fillColor: '#FF8C00', fillOpacity: 1.0, weight: 2,
      })
        .bindPopup(`<b>Substation</b>${voltage}${name}${operator}`, { maxWidth: 220 })
        .addTo(overlayGroups.substations);
    });
  } catch (err) {
    console.error('Substations fetch failed:', err);
    overlayLoaded.substations = false;  // allow retry on next toggle
  } finally {
    setOverlayLoading('substations', false);
  }
}

// Fuel type → center dot color
const PLANT_FUEL_COLOR = {
  nuclear:    '#F44336',  // red
  coal:       '#795548',  // brown
  gas:        '#FF7043',  // deep orange
  oil:        '#E64A19',  // dark orange
  wind:       '#26C6DA',  // teal
  solar:      '#FFC107',  // amber
  hydro:      '#42A5F5',  // blue
  biomass:    '#66BB6A',  // green
  geothermal: '#FF5722',  // orange-red
  waste:      '#90A4AE',  // grey-blue
};

function parseMW(str) {
  if (!str) return 0;
  const n = parseFloat(String(str).replace(/[^0-9.]/g, ''));
  return isNaN(n) ? 0 : n;
}

// Radius in meters based on output capacity — proxy for field strength
function plantEffectRadius(mw, source) {
  if (source === 'nuclear') return 12000;  // 12 km regardless of stated MW
  if (mw >= 2000) return 9000;
  if (mw >= 1000) return 7000;
  if (mw >= 500)  return 5000;
  if (mw >= 100)  return 3000;
  if (mw >  0)    return 1500;
  return 4000;  // unknown capacity — assume large
}

async function loadPowerPlants() {
  overlayLoaded.powerPlants = true;
  setOverlayLoading('powerPlants', true);
  // One-time load for CONUS + Alaska + Hawaii
  try {
    const data = await fetchOverpassData(
      `[out:json][timeout:60];(node["power"="plant"](18,-170,72,-60);way["power"="plant"](18,-170,72,-60);relation["power"="plant"](18,-170,72,-60););out center qt;`,
      70000
    );
    overlayGroups.powerPlants.clearLayers();
    data.elements.forEach((el) => {
      const lat = el.lat ?? el.center?.lat;
      const lon = el.lon ?? el.center?.lon;
      if (lat == null || lon == null) return;

      const source   = (el.tags?.['plant:source'] ?? '').toLowerCase();
      const mw       = parseMW(el.tags?.['plant:output:electricity']);
      const name     = el.tags?.name     ? escapeHtml(el.tags.name)     : 'Power Plant';
      const operator = el.tags?.operator ? escapeHtml(el.tags.operator) : '';
      const fuelColor = PLANT_FUEL_COLOR[source] ?? '#90A4AE';
      const radius    = plantEffectRadius(mw, source);
      const radiusKm  = (radius / 1000).toFixed(1);

      const fuelLabel = source
        ? source.charAt(0).toUpperCase() + source.slice(1)
        : 'Unknown';
      const popup = `<b>${name}</b>`
        + `<br>Type: ${fuelLabel}`
        + (mw   ? `<br>Capacity: ${mw} MW`      : '')
        + (operator ? `<br>Operator: ${operator}` : '')
        + `<br><span style="color:#e94560">⚠ Effect zone: ${radiusKm} km radius</span>`;

      // Effect zone — semi-transparent red circle
      L.circle([lat, lon], {
        radius,
        color:       '#e94560',
        weight:      1.5,
        opacity:     0.5,
        fillColor:   '#e94560',
        fillOpacity: 0.10,
        interactive: false,
      }).addTo(overlayGroups.powerPlants);

      // Center marker — colored by fuel type
      L.circleMarker([lat, lon], {
        radius:      12,
        color:       '#fff',
        weight:      2,
        fillColor:   fuelColor,
        fillOpacity: 1.0,
      }).bindPopup(popup, { maxWidth: 260 }).addTo(overlayGroups.powerPlants);
    });
  } catch (err) {
    console.error('Power plants fetch failed:', err);
    overlayLoaded.powerPlants = false;  // allow retry on next toggle
  } finally {
    setOverlayLoading('powerPlants', false);
  }
}

function onLayerMoveEnd() {
  if (!activeOverlays.has('powerLines') && !activeOverlays.has('substations')) return;
  clearTimeout(powerFetchTimer);
  powerFetchTimer = setTimeout(() => {
    if (activeOverlays.has('powerLines'))  loadPowerLines();
    if (activeOverlays.has('substations')) loadSubstations();
  }, 1200);  // longer debounce — reduces Overpass rate-limit hits during panning
}

// ============================================================
// 7. Location — GPS dot, Locate Me, Follow Me
// ============================================================
function initLocation() {
  if (!navigator.geolocation) {
    console.warn('Geolocation not supported');
    return;
  }

  watchId = navigator.geolocation.watchPosition(
    onPosition,
    (err) => console.warn('Geolocation error:', err.message),
    { enableHighAccuracy: true, maximumAge: 5000, timeout: 15000 }
  );

  document.getElementById('btn-locate').addEventListener('click', () => {
    if (!followMe) enableFollowMe();
    else if (locationMarker) map.setView(locationMarker.getLatLng(), map.getZoom());
  });

  document.getElementById('btn-follow').addEventListener('click', () => {
    if (followMe) disableFollowMe();
    else          enableFollowMe();
  });
}

function onPosition(pos) {
  const { latitude: lat, longitude: lng, accuracy } = pos.coords;
  const latlng = L.latLng(lat, lng);

  if (!locationMarker) {
    const icon = L.divIcon({
      html:       '<div class="location-dot-wrapper"><div class="location-dot"></div><div class="location-pulse"></div></div>',
      className:  '',
      iconSize:   [16, 16],
      iconAnchor: [8, 8],
    });
    locationMarker = L.marker(latlng, { icon, zIndexOffset: 500 }).addTo(map);
    locationMarker.on('click', L.DomEvent.stopPropagation);

    accuracyCircle = L.circle(latlng, {
      radius:      accuracy,
      color:       '#2979FF',
      fillColor:   '#2979FF',
      fillOpacity: 0.08,
      weight:      1,
    }).addTo(map);

    document.getElementById('btn-locate').classList.remove('hidden');
    document.getElementById('btn-follow').classList.remove('hidden');
    enableFollowMe();
    map.setView(latlng, 12);
  } else {
    locationMarker.setLatLng(latlng);
    accuracyCircle.setLatLng(latlng);
    accuracyCircle.setRadius(accuracy);
    if (followMe) map.setView(latlng, map.getZoom());
  }
}

function enableFollowMe() {
  followMe = true;
  const btn = document.getElementById('btn-follow');
  btn.classList.add('active');
  btn.setAttribute('aria-pressed', 'true');
  btn.setAttribute('aria-label', 'Follow Me ON — tap to stop');
  if (locationMarker) map.setView(locationMarker.getLatLng(), map.getZoom());
}

function disableFollowMe() {
  followMe = false;
  const btn = document.getElementById('btn-follow');
  btn.classList.remove('active');
  btn.setAttribute('aria-pressed', 'false');
  btn.setAttribute('aria-label', 'Toggle follow me mode');
}

// ============================================================
// 8. Map render helpers
// ============================================================
function addPinToMap(lat, lng, rating, note) {
  const color = PIN_COLORS[rating] ?? PIN_COLORS.neutral;
  const svg   = `<svg xmlns="http://www.w3.org/2000/svg" width="28" height="28" viewBox="0 0 28 28">
    <circle cx="14" cy="14" r="11" fill="${color}" fill-opacity="0.85" stroke="#fff" stroke-width="2.5"/>
  </svg>`;

  const icon = L.divIcon({
    html:        svg,
    className:   '',
    iconSize:    [28, 28],
    iconAnchor:  [14, 14],
    popupAnchor: [0, -16],
  });

  const marker = L.marker([lat, lng], { icon }).addTo(map);
  marker.bindPopup(buildPopupHtml(rating, note), { maxWidth: 240 });
  marker.on('click', L.DomEvent.stopPropagation);
  return marker;
}

function addAreaToMap(vertices, rating, note) {
  const color = PIN_COLORS[rating] ?? PIN_COLORS.neutral;

  const polygon = L.polygon(vertices, {
    color,
    fillColor:   color,
    fillOpacity: 0.2,
    weight:      2,
  }).addTo(map);

  polygon.bindPopup(buildPopupHtml(rating, note), { maxWidth: 240 });
  polygon.on('click', L.DomEvent.stopPropagation);
  return polygon;
}

function buildPopupHtml(rating, note) {
  const label   = rating.charAt(0).toUpperCase() + rating.slice(1);
  const noteHtml = note ? `<div class="popup-note">${escapeHtml(note)}</div>` : '';
  return `<div class="popup-rating ${rating}">${label}</div>${noteHtml}`;
}

// ============================================================
// 9. Data — load & save
// ============================================================
function loadAllDrawings(userId) {
  loadPins(userId);
  loadDrawings(userId);  // single 'drawings' collection covers strokes + areas
}

async function loadPins(userId) {
  if (!db) return;
  try {
    const snap = await getDocs(query(collection(db, 'pins'), where('userId', '==', userId)));
    console.log(`Loaded ${snap.size} pins`);
    snap.forEach((d) => {
      const { lat, lng, rating, note } = d.data();
      const layer = addPinToMap(lat, lng, rating, note ?? '');
      pushReviewItem({
        id: d.id, type: 'pin', rating, note: note ?? '',
        lat, lng, bounds: null, layer,
        createdAt: d.data().createdAt?.toDate() ?? new Date(0),
      });
    });
  } catch (err) { console.error('Load pins failed:', err); }
}

async function loadDrawings(userId) {
  if (!db) return;
  try {
    const snap = await getDocs(query(collection(db, 'drawings'), where('userId', '==', userId)));
    let strokes = 0, areas = 0;
    snap.forEach((d) => {
      const data = d.data();
      if (data.type === 'stroke') {
        renderSavedStroke(data.rating, data.points, d.id);
        const c = computeCentroid(data.points);
        pushReviewItem({
          id: d.id, type: 'stroke', rating: data.rating, note: '',
          lat: c.lat, lng: c.lng, bounds: null,
          createdAt: data.createdAt?.toDate() ?? new Date(0),
        });
        strokes++;
      } else if (data.type === 'area') {
        const verts = data.vertices.map(v => L.latLng(v.lat, v.lng));
        const layer = addAreaToMap(verts, data.rating, data.note ?? '');
        const bounds = L.polygon(verts).getBounds();
        const center = bounds.getCenter();
        pushReviewItem({
          id: d.id, type: 'area', rating: data.rating, note: data.note ?? '',
          lat: center.lat, lng: center.lng, bounds, layer,
          createdAt: data.createdAt?.toDate() ?? new Date(0),
        });
        areas++;
      }
    });
    console.log(`Loaded ${snap.size} drawings (${strokes} strokes, ${areas} areas)`);
  } catch (err) { console.error('Load drawings failed:', err); }
}

function renderSavedStroke(rating, points, docId) {
  const layers = points.map(({ lat, lng, r }) =>
    L.circle([lat, lng], {
      radius:      r,
      color:       'none',
      fillColor:   PAINT_FILL[rating],
      fillOpacity: PAINT_STROKE_OPACITY,
      interactive: false,
    }).addTo(map)
  );
  allStrokes.push({ layers, points, rating, docId });
}

async function savePin(userId, lat, lng, rating, note) {
  if (!db) throw new Error('Firestore not ready');
  const ref = await addDoc(collection(db, 'pins'), {
    userId, lat, lng, rating, note: note.trim(), createdAt: serverTimestamp(),
  });
  console.log('Pin saved:', ref.id);
  return ref;
}

async function saveStroke(userId, rating, points) {
  if (!db) throw new Error('Firestore not ready');
  const ref = await addDoc(collection(db, 'drawings'), {
    userId, type: 'stroke', rating, points, createdAt: serverTimestamp(),
  });
  console.log('Stroke saved:', ref.id);
  return ref;
}

async function saveArea(userId, vertices, rating, note) {
  if (!db) throw new Error('Firestore not ready');
  const plainVerts = vertices.map(v => ({ lat: v.lat, lng: v.lng }));
  const ref = await addDoc(collection(db, 'drawings'), {
    userId, type: 'area', rating, note: note.trim(), vertices: plainVerts, createdAt: serverTimestamp(),
  });
  console.log('Area saved:', ref.id);
  return ref;
}

// ============================================================
// 10. Auth
// ============================================================
async function initAuth() {
  try {
    const app = initializeApp(firebaseConfig);
    auth = getAuth(app);
    // experimentalAutoDetectLongPolling silences Safari CORS noise
    db = initializeFirestore(app, { experimentalAutoDetectLongPolling: true });
  } catch (err) {
    console.error('Firebase init failed:', err);
    return;
  }

  onAuthStateChanged(auth, (user) => {
    currentUser = user;
    updateAuthUI(user);
    if (user) {
      console.log('Signed in as:', user.displayName ?? user.email ?? user.uid);
      loadAllDrawings(user.uid);
    }
  });
}

function initAuthUI() {
  document.getElementById('btn-signin').addEventListener('click', async () => {
    if (!auth) return;
    try { await signInWithPopup(auth, new GoogleAuthProvider()); }
    catch (err) {
      if (err.code !== 'auth/popup-closed-by-user') console.error('Sign-in failed:', err);
    }
  });
  document.getElementById('btn-signout').addEventListener('click', () => signOut(auth));
}

function updateAuthUI(user) {
  const btnSignin  = document.getElementById('btn-signin');
  const userInfo   = document.getElementById('user-info');
  const userAvatar = document.getElementById('user-avatar');
  const userName   = document.getElementById('user-name');

  if (user) {
    btnSignin.classList.add('hidden');
    userInfo.classList.remove('hidden');
    userAvatar.src           = user.photoURL ?? '';
    userAvatar.style.display = user.photoURL ? '' : 'none';
    userName.textContent     = user.displayName ?? user.email ?? 'Signed in';
  } else {
    btnSignin.classList.remove('hidden');
    userInfo.classList.add('hidden');
  }
}

// ============================================================
// 11. Toolbar
// ============================================================
function initToolbar() {
  // All three buttons now active — click toggles on/off
  document.getElementById('btn-pin').addEventListener('click', () => {
    setMode(currentMode === 'pin' ? 'none' : 'pin');
  });
  document.getElementById('btn-paint').addEventListener('click', () => {
    setMode(currentMode === 'paint' ? 'none' : 'paint');
  });
  document.getElementById('btn-polygon').addEventListener('click', () => {
    setMode(currentMode === 'polygon' ? 'none' : 'polygon');
  });
}

function setMode(newMode) {
  const prevMode = currentMode;

  // Exit previous mode cleanly
  if (prevMode === 'paint')   exitPaintMode();
  if (prevMode === 'polygon') exitPolygonMode();

  currentMode = newMode;

  // Enter new mode
  if (newMode === 'paint')   enterPaintMode();
  if (newMode === 'polygon') enterPolygonMode();

  // Sync button active states
  ['pin', 'paint', 'polygon'].forEach((m) =>
    document.getElementById(`btn-${m}`).classList.toggle('active', m === newMode)
  );

  // Cursor — crosshair for drawing tools
  map.getContainer().style.cursor =
    (newMode === 'pin' || newMode === 'polygon') ? 'crosshair' : '';

  // Drawing HUD visibility
  const inDrawMode = (newMode === 'paint' || newMode === 'polygon');
  document.getElementById('drawing-hud').classList.toggle('hidden', !inDrawMode);
  if (inDrawMode) updateHudContent(newMode);
}

// ============================================================
// 12. Drawing HUD (shared panel for paint + polygon controls)
// ============================================================
function initDrawingHud() {
  // Paint: rating buttons
  document.querySelectorAll('.hud-rating-btn').forEach((btn) =>
    btn.addEventListener('click', () => setPaintRating(btn.dataset.paintRating))
  );

  // Paint: undo / clear
  document.getElementById('btn-undo-stroke').addEventListener('click', undoLastStroke);
  document.getElementById('btn-clear-strokes').addEventListener('click', clearAllStrokes);

  // Polygon: finish / cancel
  document.getElementById('btn-polygon-finish').addEventListener('click', finishPolygon);
  document.getElementById('btn-polygon-cancel').addEventListener('click', () => setMode('none'));

  // Set initial paint rating display
  setPaintRating('neutral');
}

function updateHudContent(mode) {
  document.getElementById('paint-hud-content').classList.toggle('hidden', mode !== 'paint');
  document.getElementById('polygon-hud-content').classList.toggle('hidden', mode !== 'polygon');
}

function setPaintRating(rating) {
  paintRating = rating;
  document.querySelectorAll('.hud-rating-btn').forEach((btn) => {
    const on = btn.dataset.paintRating === rating;
    btn.classList.toggle('active', on);
    btn.setAttribute('aria-pressed', String(on));
  });
}

// ============================================================
// 13. Finger Paint
// ============================================================
function enterPaintMode() {
  map.closePopup();
  map.dragging.disable();
  if (map.tap) map.tap.disable();

  const c = map.getContainer();
  c.addEventListener('pointerdown',   onPaintPointerDown);
  c.addEventListener('pointermove',   onPaintPointerMove);
  c.addEventListener('pointerup',     onPaintPointerUp);
  c.addEventListener('pointercancel', onPaintPointerUp);
}

function exitPaintMode() {
  map.dragging.enable();
  if (map.tap) map.tap.enable();

  const c = map.getContainer();
  c.removeEventListener('pointerdown',   onPaintPointerDown);
  c.removeEventListener('pointermove',   onPaintPointerMove);
  c.removeEventListener('pointerup',     onPaintPointerUp);
  c.removeEventListener('pointercancel', onPaintPointerUp);

  if (isPainting) endStroke();
  isPainting = false;
}

function onPaintPointerDown(e) {
  // Only track the primary pointer (ignore secondary fingers for pinch-zoom)
  if (!e.isPrimary) return;
  // Skip if tapping on UI elements
  if (e.target.closest('.leaflet-control, #toolbar, #auth-bar, #location-controls, #drawing-hud, #btn-layers, #layers-panel')) return;
  if (!currentUser) { nudgeSignIn(); return; }

  e.preventDefault();
  isPainting         = true;
  activeStroke       = [];
  activeStrokeLayers = [];
  lastPaintPx        = null;
  emitPaintPoint(e);
}

function onPaintPointerMove(e) {
  if (!isPainting || !e.isPrimary) return;

  const now = Date.now();
  if (now - lastPaintTime < 10) return;   // ~100fps cap

  if (lastPaintPx) {
    const dx = e.clientX - lastPaintPx.x;
    const dy = e.clientY - lastPaintPx.y;
    if (Math.hypot(dx, dy) < PAINT_MIN_DIST_PX) return;
  }

  emitPaintPoint(e);

  // Start a new stroke segment if we hit the cap
  if (activeStroke.length >= PAINT_MAX_POINTS) endStroke();
}

function onPaintPointerUp(e) {
  if (!e.isPrimary || !isPainting) return;
  isPainting = false;
  endStroke();
}

function emitPaintPoint(e) {
  const rect   = map.getContainer().getBoundingClientRect();
  const px     = e.clientX - rect.left;
  const py     = e.clientY - rect.top;
  const latlng = map.containerPointToLatLng(L.point(px, py));

  // Radius in meters — 16 px worth of geographic distance at current zoom
  const zoom   = map.getZoom();
  const mpp    = (40075016.686 * Math.abs(Math.cos(latlng.lat * Math.PI / 180))) / Math.pow(2, zoom + 8);
  const radius = Math.round(PAINT_RADIUS_PX * mpp);

  const circle = L.circle(latlng, {
    radius,
    color:       'none',
    fillColor:   PAINT_FILL[paintRating],
    fillOpacity: PAINT_STROKE_OPACITY,
    interactive: false,
  }).addTo(map);

  activeStroke.push({ lat: latlng.lat, lng: latlng.lng, r: radius });
  activeStrokeLayers.push(circle);
  lastPaintPx   = { x: e.clientX, y: e.clientY };
  lastPaintTime = Date.now();
}

async function endStroke() {
  if (activeStroke.length === 0) return;

  // Register stroke for undo before async save
  const entry = {
    layers: [...activeStrokeLayers],
    points: [...activeStroke],
    rating: paintRating,
    docId:  null,   // filled in below once Firestore confirms
  };
  allStrokes.push(entry);
  activeStroke       = [];
  activeStrokeLayers = [];

  if (db && currentUser) {
    try {
      const ref = await saveStroke(currentUser.uid, entry.rating, entry.points);
      entry.docId = ref.id;  // back-fill for undo/delete support
      const c = computeCentroid(entry.points);
      pushReviewItem({ id: ref.id, type: 'stroke', rating: entry.rating, note: '', lat: c.lat, lng: c.lng, bounds: null, createdAt: new Date() });
    } catch (err) { console.error('Stroke save failed:', err); }
  }
}

async function undoLastStroke() {
  if (allStrokes.length === 0) return;
  const stroke = allStrokes.pop();
  stroke.layers.forEach((l) => map.removeLayer(l));
  if (stroke.docId) {
    reviewItems = reviewItems.filter(r => r.id !== stroke.docId);
    if (db) {
      try { await deleteDoc(doc(db, 'drawings', stroke.docId)); }
      catch (err) { console.error('Stroke delete failed:', err); }
    }
  }
}

async function clearAllStrokes() {
  const toClear = [...allStrokes];
  allStrokes    = [];
  toClear.forEach((s) => s.layers.forEach((l) => map.removeLayer(l)));
  if (db) {
    await Promise.all(
      toClear
        .filter((s) => s.docId)
        .map((s) => deleteDoc(doc(db, 'drawings', s.docId)).catch(console.error))
    );
  }
}

// ============================================================
// 14. Polygon
// ============================================================
function initPolygon() {
  // Buttons are wired in initDrawingHud — nothing extra needed here
}

function enterPolygonMode() {
  map.closePopup();
  map.dragging.disable();
  if (map.tap) map.tap.disable();

  polygonVertices      = [];
  polygonVertexMarkers = [];
  polygonPreviewLine   = null;
  polygonRubberBand    = null;

  // Rubber band only on devices that have a pointer (desktop)
  if (window.matchMedia('(hover: hover) and (pointer: fine)').matches) {
    map.on('mousemove', onPolygonMouseMove);
  }

  updatePolygonHud();
}

function exitPolygonMode() {
  map.dragging.enable();
  if (map.tap) map.tap.enable();
  map.off('mousemove', onPolygonMouseMove);
  clearPolygonPreview();
  polygonVertices = [];
}

function clearPolygonPreview() {
  polygonVertexMarkers.forEach((m) => map.removeLayer(m));
  polygonVertexMarkers = [];
  if (polygonPreviewLine) { map.removeLayer(polygonPreviewLine); polygonPreviewLine = null; }
  if (polygonRubberBand)  { map.removeLayer(polygonRubberBand);  polygonRubberBand  = null; }
}

function onPolygonMouseMove(e) {
  if (polygonVertices.length === 0) return;
  const pts = [polygonVertices[polygonVertices.length - 1], e.latlng];
  if (!polygonRubberBand) {
    polygonRubberBand = L.polyline(pts, {
      color:       '#2979FF',
      weight:      1.5,
      dashArray:   '4 6',
      opacity:     0.7,
      interactive: false,
    }).addTo(map);
  } else {
    polygonRubberBand.setLatLngs(pts);
  }
}

function handlePolygonClick(e) {
  const latlng = e.latlng;

  // Clicking near first vertex (≥ 3 points) closes the polygon
  if (polygonVertices.length >= 3 && isNearFirstVertex(latlng)) {
    finishPolygon();
    return;
  }

  // Add a new vertex
  polygonVertices.push(latlng);
  const isFirst = polygonVertices.length === 1;

  const vm = L.circleMarker(latlng, {
    radius:      isFirst ? 8 : 5,
    color:       '#fff',
    fillColor:   isFirst ? '#2979FF' : '#e94560',
    fillOpacity: 1,
    weight:      2,
    interactive: false,
  }).addTo(map);
  polygonVertexMarkers.push(vm);

  updatePolygonPreview();
  updatePolygonHud();
}

function updatePolygonPreview() {
  if (!polygonPreviewLine) {
    polygonPreviewLine = L.polyline(polygonVertices, {
      color:       '#2979FF',
      weight:      2,
      dashArray:   '6 4',
      opacity:     0.8,
      interactive: false,
    }).addTo(map);
  } else {
    polygonPreviewLine.setLatLngs(polygonVertices);
  }
}

function isNearFirstVertex(latlng) {
  const firstPt = map.latLngToContainerPoint(polygonVertices[0]);
  const clickPt = map.latLngToContainerPoint(latlng);
  return firstPt.distanceTo(clickPt) <= 15;
}

function updatePolygonHud() {
  const hintEl    = document.getElementById('polygon-hint');
  const finishBtn = document.getElementById('btn-polygon-finish');
  const n         = polygonVertices.length;

  if (n === 0) {
    hintEl.textContent = 'Tap map to place first point';
    finishBtn.classList.add('hidden');
  } else if (n < 3) {
    hintEl.textContent = `${n} point${n > 1 ? 's' : ''} — need ${3 - n} more`;
    finishBtn.classList.add('hidden');
  } else {
    hintEl.textContent = `${n} points — tap first point or Finish`;
    finishBtn.classList.remove('hidden');
    // Make the first vertex visually indicate it can be clicked to close
    const firstEl = polygonVertexMarkers[0]?.getElement();
    if (firstEl) firstEl.style.cursor = 'pointer';
  }
}

function finishPolygon() {
  if (polygonVertices.length < 3) return;
  const vertices = [...polygonVertices];
  exitPolygonMode();  // clears preview layers; keeps currentMode as 'polygon'
  openModal({ type: 'polygon', vertices });
}

// ============================================================
// 15. Map click router
// ============================================================
function onMapClick(e) {
  if (currentMode === 'none' || currentMode === 'paint') return;

  if (currentMode === 'polygon') {
    handlePolygonClick(e);
    return;
  }

  if (currentMode === 'pin') {
    if (!currentUser) { nudgeSignIn(); return; }
    openModal({ type: 'pin', latlng: e.latlng });
  }
}

function nudgeSignIn() {
  const btn = document.getElementById('btn-signin');
  btn.classList.remove('nudge');
  void btn.offsetWidth;         // force reflow to restart animation
  btn.classList.add('nudge');
}

// ============================================================
// 16. Modal
// ============================================================
function initModal() {
  const overlay    = document.getElementById('modal-overlay');
  const btnCancel  = document.getElementById('btn-cancel');
  const btnSave    = document.getElementById('btn-save');
  const ratingBtns = document.querySelectorAll('.rating-btn');
  const noteInput  = document.getElementById('note-input');

  ratingBtns.forEach((btn) => {
    btn.addEventListener('click', () => {
      ratingBtns.forEach((b) => { b.classList.remove('selected'); b.setAttribute('aria-pressed', 'false'); });
      btn.classList.add('selected');
      btn.setAttribute('aria-pressed', 'true');
      selectedRating = btn.dataset.rating;
      updateSaveButtonState();
    });
  });

  btnCancel.addEventListener('click', closeModal);

  overlay.addEventListener('click', (ev) => {
    if (ev.target === overlay) closeModal();
  });

  document.addEventListener('keydown', (ev) => {
    if (ev.key === 'Escape' && !overlay.classList.contains('hidden')) closeModal();
  });

  // Save — optimistic close then persist in background
  btnSave.addEventListener('click', async () => {
    if (!selectedRating || !modalContext || !currentUser) return;

    const ctx    = modalContext;
    const rating = selectedRating;
    const note   = noteInput.value;

    closeModal();

    if (ctx.type === 'pin') {
      const { lat, lng } = ctx.latlng;
      const layer = addPinToMap(lat, lng, rating, note);
      try {
        const ref = await savePin(currentUser.uid, lat, lng, rating, note);
        pushReviewItem({ id: ref.id, type: 'pin', rating, note, lat, lng, bounds: null, layer, createdAt: new Date() });
      }
      catch (err) { console.error('Pin save failed:', err); }

    } else if (ctx.type === 'polygon') {
      const layer = addAreaToMap(ctx.vertices, rating, note);
      try {
        const ref = await saveArea(currentUser.uid, ctx.vertices, rating, note);
        const bounds = L.polygon(ctx.vertices).getBounds();
        const center = bounds.getCenter();
        pushReviewItem({ id: ref.id, type: 'area', rating, note, lat: center.lat, lng: center.lng, bounds, layer, createdAt: new Date() });
      }
      catch (err) { console.error('Area save failed:', err); }
      // Return to polygon mode so user can draw another area
      setMode('polygon');

    } else if (ctx.type === 'edit-note') {
      const item = reviewItems[ctx.idx];
      item.note = note.trim();
      if (item.layer) item.layer.setPopupContent(buildPopupHtml(item.rating, item.note));
      try {
        const col = item.type === 'pin' ? 'pins' : 'drawings';
        await updateDoc(doc(db, col, item.id), { note: item.note });
      } catch (err) { console.error('Note update failed:', err); }
      renderReviewList();
    }
  });
}

function openModal(context) {
  modalContext   = context;
  selectedRating = null;

  const isEditNote = context.type === 'edit-note';
  const isPolygon  = context.type === 'polygon';

  document.getElementById('modal-title').textContent =
    isEditNote ? 'Edit Note' : isPolygon ? 'Rate This Area' : 'Rate This Location';
  document.getElementById('btn-save').textContent =
    isEditNote ? 'Save Note' : isPolygon ? 'Save Area' : 'Save Pin';

  // Show/hide rating buttons — not needed when just editing a note
  document.querySelector('.rating-group').classList.toggle('hidden', isEditNote);

  document.querySelectorAll('.rating-btn').forEach((b) => {
    b.classList.remove('selected');
    b.setAttribute('aria-pressed', 'false');
  });

  if (isEditNote) {
    document.getElementById('note-input').value = context.item.note ?? '';
    selectedRating = context.item.rating;  // keep existing rating; enables save button
    document.getElementById('btn-save').disabled = false;
    document.getElementById('note-input').focus();
  } else {
    document.getElementById('note-input').value  = '';
    document.getElementById('btn-save').disabled = true;
    document.querySelectorAll('.rating-btn')[0]?.focus();
  }

  document.getElementById('modal-overlay').classList.remove('hidden');
}

function closeModal() {
  document.getElementById('modal-overlay').classList.add('hidden');
  modalContext   = null;
  selectedRating = null;
}

function updateSaveButtonState() {
  document.getElementById('btn-save').disabled = (selectedRating === null);
}

// ============================================================
// 17. Utility
// ============================================================
function escapeHtml(str) {
  return str
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

// ============================================================
// 19. Notes Panel
// ============================================================

// SVG icon paths for review list
const REVIEW_ICONS = {
  pin: `<svg class="review-type-icon" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5s1.12-2.5 2.5-2.5 2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z"/></svg>`,
  stroke: `<svg class="review-type-icon" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M7 14c-1.66 0-3 1.34-3 3 0 1.31-1.16 2-2 2 .92 1.22 2.49 2 4 2 2.21 0 4-1.79 4-4 0-1.66-1.34-3-3-3zm13.71-9.37l-1.34-1.34a1 1 0 0 0-1.41 0L9 12.25 11.75 15l8.96-8.96a1 1 0 0 0 0-1.41z"/></svg>`,
  area: `<svg class="review-type-icon" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M17 1L7 6v13l10 4 7-4V5l-7-4zm0 2.18L22 6v10l-5 2.82L7 16.18V7.18L17 3.18zM2 8v12l5 2v-2.5L4 18V9.5L2 8z"/></svg>`,
};

function initNotesPanel() {
  const btnNotes = document.getElementById('btn-notes');
  btnNotes.addEventListener('click', (e) => {
    e.stopPropagation();
    const panel = document.getElementById('notes-panel');
    if (panel.classList.contains('hidden')) {
      openNotesPanel();
    } else {
      closeNotesPanel();
    }
  });

  document.getElementById('btn-notes-close').addEventListener('click', closeNotesPanel);

  // Escape key
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && !document.getElementById('notes-panel').classList.contains('hidden')) {
      closeNotesPanel();
    }
  });

  // Click outside — but not when the edit modal is open
  document.addEventListener('click', (e) => {
    const panel  = document.getElementById('notes-panel');
    const btnN   = document.getElementById('btn-notes');
    const modal  = document.getElementById('modal-overlay');
    if (!panel.classList.contains('hidden') &&
        !panel.contains(e.target) &&
        !btnN.contains(e.target) &&
        modal.classList.contains('hidden')) {
      closeNotesPanel();
    }
  });
}

function openNotesPanel() {
  renderReviewList();
  document.getElementById('notes-panel').classList.remove('hidden');
  const btn = document.getElementById('btn-notes');
  btn.classList.add('active');
  btn.setAttribute('aria-expanded', 'true');
}

function closeNotesPanel() {
  document.getElementById('notes-panel').classList.add('hidden');
  const btn = document.getElementById('btn-notes');
  btn.classList.remove('active');
  btn.setAttribute('aria-expanded', 'false');
}

async function deleteItem(idx) {
  const item = reviewItems[idx];
  if (!item || !currentUser) return;

  // Remove from map
  if (item.type === 'stroke') {
    const si = allStrokes.findIndex(s => s.docId === item.id);
    if (si !== -1) {
      allStrokes[si].layers.forEach(l => map.removeLayer(l));
      allStrokes.splice(si, 1);
    }
  } else if (item.layer) {
    map.removeLayer(item.layer);
  }

  // Remove from Firestore
  try {
    const col = item.type === 'pin' ? 'pins' : 'drawings';
    await deleteDoc(doc(db, col, item.id));
  } catch (err) { console.error('Delete failed:', err); }

  // Remove from list and re-render
  reviewItems.splice(idx, 1);
  renderReviewList();
}

const PENCIL_SVG = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" width="13" height="13" fill="currentColor" aria-hidden="true"><path d="M3 17.25V21h3.75L17.81 9.94l-3.75-3.75L3 17.25zM20.71 7.04a1 1 0 0 0 0-1.41l-2.34-2.34a1 1 0 0 0-1.41 0l-1.83 1.83 3.75 3.75 1.83-1.83z"/></svg>`;
const TRASH_SVG  = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" width="13" height="13" fill="currentColor" aria-hidden="true"><path d="M6 19c0 1.1.9 2 2 2h8c1.1 0 2-.9 2-2V7H6v12zM19 4h-3.5l-1-1h-5l-1 1H5v2h14V4z"/></svg>`;

function renderReviewList() {
  const list = document.getElementById('notes-list');

  if (reviewItems.length === 0) {
    list.innerHTML = '<p class="review-empty">No notes yet — drop a pin or draw an area to get started.</p>';
    return;
  }

  list.innerHTML = reviewItems.map((item, idx) => {
    const icon     = REVIEW_ICONS[item.type] ?? '';
    const noteText = item.note ? escapeHtml(item.note) : '';
    const dateText = relativeTime(item.createdAt);
    const canEdit  = item.type !== 'stroke';  // strokes have no note to edit
    const editBtn  = canEdit
      ? `<button class="review-action-btn review-edit-btn" data-idx="${idx}" aria-label="Edit note">${PENCIL_SVG}</button>`
      : '';
    return `<div class="review-item">
      <div class="review-item-main" data-idx="${idx}">
        <span class="review-dot review-dot--${escapeHtml(item.rating)}"></span>
        ${icon}
        <span class="review-body">
          <span class="review-location" data-idx="${idx}">…</span>
          <span class="review-note">${noteText}</span>
        </span>
        <span class="review-date">${dateText}</span>
      </div>
      <div class="review-actions">
        ${editBtn}
        <button class="review-action-btn review-delete-btn" data-idx="${idx}" aria-label="Delete">${TRASH_SVG}</button>
      </div>
    </div>`;
  }).join('');

  // Fly-to on main area click
  list.querySelectorAll('.review-item-main').forEach((el) => {
    el.addEventListener('click', () => {
      const idx = parseInt(el.dataset.idx, 10);
      flyToItem(reviewItems[idx]);
    });
  });

  // Edit note
  list.querySelectorAll('.review-edit-btn').forEach((btn) => {
    btn.addEventListener('click', () => {
      const idx = parseInt(btn.dataset.idx, 10);
      openModal({ type: 'edit-note', item: reviewItems[idx], idx });
    });
  });

  // Delete
  list.querySelectorAll('.review-delete-btn').forEach((btn) => {
    btn.addEventListener('click', () => {
      const idx = parseInt(btn.dataset.idx, 10);
      const item = reviewItems[idx];
      const label = item.type === 'pin' ? 'pin' : item.type === 'area' ? 'area' : 'paint stroke';
      if (confirm(`Delete this ${label}? This cannot be undone.`)) {
        deleteItem(idx);
      }
    });
  });

  // Kick off async geocoding
  geocodeAllVisible();
}

async function geocodeAllVisible() {
  const spans = document.querySelectorAll('#notes-list .review-location[data-idx]');
  for (const span of spans) {
    const idx  = parseInt(span.dataset.idx, 10);
    const item = reviewItems[idx];
    if (!item) continue;
    const key = `${item.lat.toFixed(3)},${item.lng.toFixed(3)}`;
    if (geocodeCache[key]) {
      span.textContent = geocodeCache[key];
    } else {
      try {
        const name = await reverseGeocode(item.lat, item.lng);
        geocodeCache[key] = name;
        // Span may be stale if panel was re-rendered; query again by key
        document.querySelectorAll(`#notes-list .review-location[data-idx="${idx}"]`).forEach(el => {
          el.textContent = name;
        });
      } catch { /* keep '…' */ }
      await new Promise(r => setTimeout(r, 300));  // 300ms between Nominatim requests
    }
  }
}

async function reverseGeocode(lat, lng) {
  const url = `https://nominatim.openstreetmap.org/reverse?lat=${lat}&lon=${lng}&format=json&zoom=10`;
  const resp = await fetch(url, {
    headers: {
      'Accept-Language': 'en',
      'User-Agent': 'relocation-map',
    },
  });
  if (!resp.ok) throw new Error(`Nominatim error: ${resp.status}`);
  const data = await resp.json();
  const addr = data.address ?? {};
  const city  = addr.city ?? addr.town ?? addr.village ?? addr.county ?? '';
  const state = addr.state ?? '';
  if (city && state) return `${city}, ${state}`;
  if (city)  return city;
  if (state) return state;
  return 'Unknown';
}

function flyToItem(item) {
  closeNotesPanel();
  if (item.bounds) {
    map.flyToBounds(item.bounds, { padding: [60, 60], maxZoom: 14 });
  } else {
    map.flyTo([item.lat, item.lng], 13);
  }
}

// ============================================================
// 18. Bootstrap
// ============================================================
(async function bootstrap() {
  initMap();
  initLayers();       // adds base tile layer + wires layer panel
  initLocation();
  initDrawingHud();   // wire HUD buttons before modes reference them
  initPolygon();
  initToolbar();
  initModal();
  initNotesPanel();   // Sprint 5 — notes & review panel
  initAuthUI();
  setMode('none');
  await initAuth();   // last — pins/strokes/areas render after map is ready
})();

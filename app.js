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
    maxZoom: 19,
  }),
  satellite: L.tileLayer(
    'https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',
    { attribution: '&copy; <a href="https://www.esri.com/">Esri</a>', maxZoom: 19 }
  ),
  terrain: L.tileLayer('https://{s}.tile.opentopomap.org/{z}/{x}/{y}.png', {
    attribution: '&copy; <a href="https://opentopomap.org">OpenTopoMap</a>',
    maxZoom: 17,
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

// — Layers —
let activeBaseTileLayer = null;
let activeBaseLayerName = 'street';

const overlayGroups = {
  powerLines:  L.layerGroup(),
  substations: L.layerGroup(),
  nexrad:      L.layerGroup(),
  military:    L.layerGroup(),
};
const overlayLoaded  = { powerLines: false, substations: false, nexrad: false, military: false };
const activeOverlays = new Set();
let   powerFetchTimer = null;

// ============================================================
// 6. initMap
// ============================================================
function initMap() {
  map = L.map('map', {
    center:      [37.0, -80.0],
    zoom:        6,
    zoomControl: false,
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
    // Viewport-based overlays must re-fetch fresh data on next toggle-ON
    if (key === 'powerLines' || key === 'substations') overlayLoaded[key] = false;
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
    case 'nexrad':      return loadNexrad();
    case 'military':    return loadMilitaryRadar();
  }
}

async function fetchOverpassData(query) {
  const resp = await fetch('https://overpass-api.de/api/interpreter', {
    method:  'POST',
    headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
    body:    `data=${encodeURIComponent(query)}`,
  });
  if (!resp.ok) throw new Error(`Overpass error: ${resp.status}`);
  return resp.json();
}

async function loadPowerLines() {
  overlayGroups.powerLines.clearLayers();

  if (map.getZoom() < 7) {
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
  const b    = map.getBounds();
  const bbox = `${b.getSouth()},${b.getWest()},${b.getNorth()},${b.getEast()}`;
  try {
    const data = await fetchOverpassData(
      `[out:json][timeout:25];way["power"="line"](${bbox});out geom;`
    );
    data.elements.forEach((el) => {
      if (!el.geometry?.length) return;
      const coords   = el.geometry.map((p) => [p.lat, p.lon]);
      const voltage  = el.tags?.voltage  ? `<br>Voltage: ${el.tags.voltage} V`          : '';
      const name     = el.tags?.name     ? `<br>${escapeHtml(el.tags.name)}`             : '';
      const operator = el.tags?.operator ? `<br>Op: ${escapeHtml(el.tags.operator)}`    : '';
      L.polyline(coords, { color: '#FF8C00', weight: 2, opacity: 0.85 })
        .bindPopup(`<b>Power Line</b>${voltage}${name}${operator}`, { maxWidth: 220 })
        .addTo(overlayGroups.powerLines);
    });
  } catch (err) { console.error('Power lines fetch failed:', err); }
}

async function loadSubstations() {
  overlayGroups.substations.clearLayers();
  if (map.getZoom() < 7) return;

  overlayLoaded.substations = true;
  const b    = map.getBounds();
  const bbox = `${b.getSouth()},${b.getWest()},${b.getNorth()},${b.getEast()}`;
  try {
    const data = await fetchOverpassData(
      `[out:json][timeout:25];(node["power"="substation"](${bbox});way["power"="substation"](${bbox}););out center;`
    );
    data.elements.forEach((el) => {
      const lat = el.lat ?? el.center?.lat;
      const lon = el.lon ?? el.center?.lon;
      if (lat == null || lon == null) return;
      const voltage  = el.tags?.voltage  ? `<br>Voltage: ${el.tags.voltage} V`       : '';
      const name     = el.tags?.name     ? `<br>${escapeHtml(el.tags.name)}`          : '';
      const operator = el.tags?.operator ? `<br>Op: ${escapeHtml(el.tags.operator)}` : '';
      L.circleMarker([lat, lon], {
        radius: 6, color: '#FF8C00', fillColor: '#FF8C00', fillOpacity: 0.85, weight: 2,
      })
        .bindPopup(`<b>Substation</b>${voltage}${name}${operator}`, { maxWidth: 220 })
        .addTo(overlayGroups.substations);
    });
  } catch (err) { console.error('Substations fetch failed:', err); }
}

async function loadNexrad() {
  overlayLoaded.nexrad = true;
  const radarSvg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" width="16" height="16" fill="#2979FF" aria-hidden="true"><path d="M1 9l2 2c4.97-4.97 13.03-4.97 18 0l2-2C16.93 2.93 7.08 2.93 1 9zm8 8l3 3 3-3c-1.65-1.66-4.34-1.66-6 0zm-4-4l2 2c2.76-2.76 7.24-2.76 10 0l2-2C15.14 9.14 8.87 9.14 5 13z"/></svg>`;
  try {
    const data = await fetchOverpassData(
      `[out:json][timeout:30];node["man_made"="monitoring_station"]["monitoring:weather"="yes"](18,-130,50,-60);out;`
    );
    data.elements.forEach((el) => {
      const name  = el.tags?.name ?? (el.tags?.ref ? `NEXRAD ${el.tags.ref}` : 'Weather Station');
      const ref   = el.tags?.ref  ?? '';
      const city  = el.tags?.['addr:city']  ?? '';
      const state = el.tags?.['addr:state'] ?? '';
      const popup = `<b>${escapeHtml(name)}</b>` +
        (ref && ref !== name ? `<br>ID: ${escapeHtml(ref)}` : '') +
        (city  ? `<br>${escapeHtml(city)}`   : '') +
        (state ? `, ${escapeHtml(state)}`    : '');
      L.marker([el.lat, el.lon], {
        icon: L.divIcon({
          html:        `<div class="nexrad-icon">${radarSvg}</div>`,
          className:   '',
          iconSize:    [26, 26],
          iconAnchor:  [13, 13],
          popupAnchor: [0, -15],
        }),
      }).bindPopup(popup, { maxWidth: 220 }).addTo(overlayGroups.nexrad);
    });
    console.log(`NEXRAD: loaded ${data.elements.length} stations`);
  } catch (err) { console.error('NEXRAD fetch failed:', err); }
}

async function loadMilitaryRadar() {
  overlayLoaded.military = true;
  const shieldSvg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" width="16" height="16" fill="#6B8E23" aria-hidden="true"><path d="M12 1L3 5v6c0 5.55 3.84 10.74 9 12 5.16-1.26 9-6.45 9-12V5l-9-4z"/></svg>`;
  try {
    const data = await fetchOverpassData(
      `[out:json][timeout:30];(node["military"="radar"];way["military"="radar"];);out center;`
    );
    data.elements.forEach((el) => {
      const lat  = el.lat ?? el.center?.lat;
      const lon  = el.lon ?? el.center?.lon;
      if (lat == null || lon == null) return;
      const name = el.tags?.name ?? 'Military Radar';
      const desc = el.tags?.description ?? '';
      const popup = `<b>${escapeHtml(name)}</b>${desc ? `<br>${escapeHtml(desc)}` : ''}`;
      L.marker([lat, lon], {
        icon: L.divIcon({
          html:        `<div class="military-icon">${shieldSvg}</div>`,
          className:   '',
          iconSize:    [26, 26],
          iconAnchor:  [13, 13],
          popupAnchor: [0, -15],
        }),
      }).bindPopup(popup, { maxWidth: 220 }).addTo(overlayGroups.military);
    });
    console.log(`Military: loaded ${data.elements.length} radar sites`);
  } catch (err) { console.error('Military radar fetch failed:', err); }
}

function onLayerMoveEnd() {
  if (!activeOverlays.has('powerLines') && !activeOverlays.has('substations')) return;
  clearTimeout(powerFetchTimer);
  powerFetchTimer = setTimeout(() => {
    if (activeOverlays.has('powerLines'))  loadPowerLines();
    if (activeOverlays.has('substations')) loadSubstations();
  }, 600);
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
      addPinToMap(lat, lng, rating, note ?? '');
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
        strokes++;
      } else if (data.type === 'area') {
        addAreaToMap(data.vertices.map(v => L.latLng(v.lat, v.lng)), data.rating, data.note ?? '');
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
    } catch (err) { console.error('Stroke save failed:', err); }
  }
}

async function undoLastStroke() {
  if (allStrokes.length === 0) return;
  const stroke = allStrokes.pop();
  stroke.layers.forEach((l) => map.removeLayer(l));
  if (stroke.docId && db) {
    try { await deleteDoc(doc(db, 'drawings', stroke.docId)); }
    catch (err) { console.error('Stroke delete failed:', err); }
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
      addPinToMap(lat, lng, rating, note);
      try { await savePin(currentUser.uid, lat, lng, rating, note); }
      catch (err) { console.error('Pin save failed:', err); }

    } else if (ctx.type === 'polygon') {
      addAreaToMap(ctx.vertices, rating, note);
      try { await saveArea(currentUser.uid, ctx.vertices, rating, note); }
      catch (err) { console.error('Area save failed:', err); }
      // Return to polygon mode so user can draw another area
      setMode('polygon');
    }
  });
}

function openModal(context) {
  modalContext   = context;
  selectedRating = null;

  const isPolygon = context.type === 'polygon';
  document.getElementById('modal-title').textContent = isPolygon ? 'Rate This Area' : 'Rate This Location';
  document.getElementById('btn-save').textContent    = isPolygon ? 'Save Area' : 'Save Pin';

  document.querySelectorAll('.rating-btn').forEach((b) => {
    b.classList.remove('selected');
    b.setAttribute('aria-pressed', 'false');
  });

  document.getElementById('note-input').value  = '';
  document.getElementById('btn-save').disabled = true;
  document.getElementById('modal-overlay').classList.remove('hidden');
  document.querySelectorAll('.rating-btn')[0]?.focus();
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
// 18. Bootstrap
// ============================================================
(async function bootstrap() {
  initMap();
  initLayers();     // adds base tile layer + wires layer panel
  initLocation();
  initDrawingHud();   // wire HUD buttons before modes reference them
  initPolygon();
  initToolbar();
  initModal();
  initAuthUI();
  setMode('none');
  await initAuth();   // last — pins/strokes/areas render after map is ready
})();

const CACHE_NAME = 'seahaven-v1';
const FILES_TO_CACHE = [
  './',
  './index.html',
  './manifest.json',
  './seahaven.js',
  './seahaven.css',
  './seahaven-icon.png',
  './solver.js',
  './solver.wasm'
];

// Installation: alle Dateien cachen
self.addEventListener('install', e => {
  e.waitUntil(
    caches.open(CACHE_NAME).then(cache => cache.addAll(FILES_TO_CACHE))
  );
});

// Fetch: zuerst Cache, dann Netzwerk
self.addEventListener('fetch', e => {
  e.respondWith(
    caches.match(e.request).then(response => response || fetch(e.request))
  );
});


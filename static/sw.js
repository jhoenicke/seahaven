const CACHE_NAME = 'seahaven-v2';
const FILES_TO_CACHE = [
  './',
  './online.html',
  './manifest.json',
  './seahaven.js',
  './seahaven.css',
  './seahaven-icon.png',
  './solver.js',
  './solver.wasm'
];

// Installation: cache all files
self.addEventListener('install', e => {
  e.waitUntil(
    caches.open(CACHE_NAME).then(cache => cache.addAll(FILES_TO_CACHE))
  );
});

// Activation: delete caches from previous versions
self.addEventListener('activate', e => {
  e.waitUntil(
    caches.keys().then(keys =>
      Promise.all(keys.filter(k => k !== CACHE_NAME).map(k => caches.delete(k)))
    )
  );
});

// Fetch: serve from cache, fall back to network
self.addEventListener('fetch', e => {
  e.respondWith(
    caches.match(e.request).then(response => response || fetch(e.request))
  );
});


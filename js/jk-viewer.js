/*
 * JK3D — floating GLB viewer for the Joram Kai portfolio.
 *
 * Performance model
 *  - "own" views (hero, project page) get a dedicated WebGL renderer that draws straight
 *    into their canvas: no GPU→2D copies, full frame rate.
 *  - All other views share one renderer and are copied into 2D canvases; they render only
 *    when something changes (tween, drag, hover), never on an idle loop.
 *  - Model builds are queued and run one per frame-slot so scrolling never stacks them.
 *
 * JK3D.mount(canvasEl, opts) -> { setMode, setActive, reset, dispose }
 *   src, mode ('wire'|'surface'|'exploded'), surface ('auto'|'original'|'neutral'), palette,
 *   yaw, pitch, fit, gizmo, priority, own, active, lens, lensR, onStatus(s)
 */
(function () {
  'use strict';
  var G = (window.JK3D = window.JK3D || {});
  if (G.mount) return;

  var hasGL = (function () {
    try {
      var c = document.createElement('canvas');
      return !!(window.WebGLRenderingContext && (c.getContext('webgl2') || c.getContext('webgl')));
    } catch (e) { return false; }
  })();
  G.supported = hasGL && !!window.THREE && !!(window.THREE && THREE.GLTFLoader);
  var reduced = false, isCoarse = false;
  try { reduced = window.matchMedia('(prefers-reduced-motion: reduce)').matches; } catch (e) {}
  try { isCoarse = window.matchMedia('(pointer: coarse)').matches; } catch (e) {}
  G.reducedMotion = reduced;

  var shared = null, views = [], cache = {}, edgeCache = {}, wireCache = {};
  var raf = 0, lastT = 0, pointer = { x: 0, y: 0 }, queue = [], active = 0, buildQ = [], building = false;
  var MAX_LOADS = 1;

  function lin(hex) { return new THREE.Color(hex).convertSRGBToLinear(); }
  function clamp(x, a, b) { return x < a ? a : x > b ? b : x; }
  function ease(t) { return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2; }
  function lerp(a, b, t) { return a + (b - a) * t; }
  function damp(a, b, k, dt) { return lerp(a, b, 1 - Math.exp(-k * dt)); }

  function makeRenderer(canvas) {
    var R = new THREE.WebGLRenderer({ canvas: canvas || undefined, antialias: true, alpha: true, powerPreference: 'high-performance' });
    R.setPixelRatio(1);
    R.outputEncoding = THREE.sRGBEncoding;
    R.toneMapping = THREE.ACESFilmicToneMapping;
    R.toneMappingExposure = 1.05;
    R.localClippingEnabled = true;
    R.autoClear = false;
    R.setClearColor(0x000000, 0);
    R.__w = 0; R.__h = 0;
    try {
      var pm = new THREE.PMREMGenerator(R);
      R.__env = pm.fromScene(new THREE.RoomEnvironment(), 0.04).texture;
      pm.dispose();
    } catch (e) { R.__env = null; }
    return R;
  }
  function sharedRenderer() { if (!shared) shared = makeRenderer(null); return shared; }

  /* ---------- loading: embedded models first, queued ---------- */
  function embedded(url) {
    var m = window.JK_MODELS || {};
    var k = String(url).replace(/^\.\//, '');
    return m[k] || m[k.replace(/\.wasm$/, '')] || null;
  }
  function b64ToBuffer(b64) {
    var bin = atob(b64), n = bin.length, out = new Uint8Array(n);
    for (var i = 0; i < n; i++) out[i] = bin.charCodeAt(i);
    return out.buffer;
  }
  function load(url, prio, onProgress) {
    if (cache[url]) return cache[url];
    cache[url] = new Promise(function (resolve, reject) {
      queue.push({ url: url, prio: prio == null ? 5 : prio, resolve: resolve, reject: reject, onProgress: onProgress });
      queue.sort(function (a, b) { return a.prio - b.prio; });
      pump();
    });
    return cache[url];
  }
  function idle(fn) {
    if (window.requestIdleCallback) requestIdleCallback(fn, { timeout: 300 }); else setTimeout(fn, 16);
  }
  function pump() {
    while (active < MAX_LOADS && queue.length) {
      (function (job) {
        active++;
        var done = function (g) { active--; job.resolve(g); idle(pump); };
        var fail = function (e) { active--; delete cache[job.url]; job.reject(e); idle(pump); };
        var b64 = embedded(job.url);
        if (b64) {
          idle(function () {
            try {
              if (job.onProgress) job.onProgress(0.5);
              new THREE.GLTFLoader().parse(b64ToBuffer(b64), '', done, fail);
            } catch (e) { fail(e); }
          });
          return;
        }
        new THREE.GLTFLoader().load(job.url, done, function (e) {
          if (e && e.total && job.onProgress) job.onProgress(e.loaded / e.total);
        }, fail);
      })(queue.shift());
    }
  }
  /* builds (material + edge generation) run one at a time in idle slots */
  function queueBuild(fn) { buildQ.push(fn); if (!building) nextBuild(); }
  function nextBuild() {
    var fn = buildQ.shift();
    if (!fn) { building = false; return; }
    building = true;
    idle(function () { try { fn(); } catch (e) {} setTimeout(nextBuild, 30); });
  }

  /* ---------- geometry helpers ---------- */
  function edgesFor(geo, angle) {
    var k = geo.uuid + ':' + angle;
    if (!edgeCache[k]) edgeCache[k] = new THREE.EdgesGeometry(geo, angle);
    return edgeCache[k];
  }
  function wireFor(geo) {
    if (!wireCache[geo.uuid]) wireCache[geo.uuid] = new THREE.WireframeGeometry(geo);
    return wireCache[geo.uuid];
  }
  function triCount(geo) {
    var i = geo.index;
    return Math.round((i ? i.count : geo.attributes.position.count) / 3);
  }
  function unsuitable(m) {
    if (!m) return true;
    if (m.map || m.normalMap) return false;
    return (m.metalness !== undefined && m.metalness >= 0.99 && m.roughness >= 0.99);
  }
  /* screen-space lens: fragments inside/outside a circle are discarded per material group */
  function lensify(mat, uni) {
    mat.onBeforeCompile = function (shader) {
      shader.uniforms.uLens = uni;
      shader.fragmentShader = shader.fragmentShader.replace('void main() {',
        'uniform vec4 uLens;\nvoid main() {\n  if (uLens.z > 0.0) { bool jkIn = distance(gl_FragCoord.xy, uLens.xy) < uLens.z; if (jkIn != (uLens.w > 0.5)) discard; }');
    };
    mat.customProgramCacheKey = function () { return 'jk-lens'; };
  }

  /* ---------- View ---------- */
  function View(canvas, o) {
    this.c = canvas; this.o = o || {};
    this.own = !!this.o.own;
    this.status = 'idle';
    this.ready = false; this.visible = false; this.dead = false;
    this.yaw0 = o.yaw != null ? o.yaw : -0.65; this.pitch0 = o.pitch != null ? o.pitch : 0.28;
    this.yaw = this.yaw0; this.pitch = this.pitch0; this.vy = 0; this.vp = 0;
    this.zoom = 1; this.zoomT = 1; this.resetting = false;
    this.panX = 0; this.panY = 0; this.panXT = 0; this.panYT = 0;
    this.tiltX = 0; this.tiltY = 0;
    this.active = o.active !== false;
    this.spinK = this.active ? 1 : 0; this.lastInteract = -1e9;
    this.phase = Math.random() * 6.28; this.fl = 0;
    this.reveal = o.mode === 'wire' || !o.mode ? 0 : 1;
    this.explode = o.mode === 'exploded' ? 1 : 0;
    this.tw = {}; this.explodable = false;
    this.pointers = {}; this.engaged = false; this.dragging = false;
    this.mode = o.mode || 'wire';
    this.lens = !!o.lens && this.own && !isCoarse;
    this.lr = 0; this.lx = 0; this.ly = 0; this.lensOn = false;
    this.dpr = Math.min(window.devicePixelRatio || 1, this.own ? (isCoarse ? 1.5 : 1.75) : (isCoarse ? 1.25 : 1.5));
    this.interactive = o.interactive !== false;
    this.dirty = true;
    this.setup();
  }

  View.prototype.emit = function (s) {
    this.status = s.status;
    if (this.o.onStatus) { try { this.o.onStatus(s); } catch (e) {} }
  };

  View.prototype.setup = function () {
    var self = this, c = this.c;
    this.scene = new THREE.Scene();
    this.cam = new THREE.PerspectiveCamera(28, 1, 0.01, 100);
    var hemi = new THREE.HemisphereLight(0xffffff, 0x0b0d0d, 0.55);
    var key = new THREE.DirectionalLight(0xffffff, 1.6); key.position.set(2.5, 3.5, 2.2);
    var rim = new THREE.DirectionalLight(0x9fd6d9, 0.7); rim.position.set(-3, 1.2, -2.5);
    this.scene.add(hemi, key, rim);

    this.planeS = new THREE.Plane(new THREE.Vector3(0, -1, 0), 0);
    this.planeW = new THREE.Plane(new THREE.Vector3(0, 1, 0), 0);
    this.uS = { value: new THREE.Vector4(0, 0, 0, 0) };
    this.uW = { value: new THREE.Vector4(0, 0, 0, 1) };

    var pts = [];
    for (var i = 0; i <= 96; i++) { var a = i / 96 * Math.PI * 2; pts.push(new THREE.Vector3(Math.cos(a) * 0.72, 0, Math.sin(a) * 0.72)); }
    this.ring = new THREE.LineLoop(new THREE.BufferGeometry().setFromPoints(pts),
      new THREE.LineBasicMaterial({ color: lin('#00A3AB'), transparent: true, opacity: 0, toneMapped: false, depthWrite: false }));
    this.scene.add(this.ring);

    if (this.o.gizmo) this.makeGizmo();
    if (this.lens) this.makeLensRing();

    if (!this.own) this.ctx = c.getContext('2d');

    this.resize();
    if (window.ResizeObserver) {
      this.ro = new ResizeObserver(function () { self.resize(); start(); });
      this.ro.observe(c);
    }
    if (window.IntersectionObserver) {
      this.ioNear = new IntersectionObserver(function (es) {
        es.forEach(function (e) { if (e.isIntersecting) self.load(); });
      }, { rootMargin: '700px 0px' });
      this.ioVis = new IntersectionObserver(function (es) {
        es.forEach(function (e) { self.visible = e.isIntersecting; if (self.visible) { self.dirty = true; start(); } });
      }, { rootMargin: '40px 0px' });
      this.ioNear.observe(c); this.ioVis.observe(c);
    } else { this.visible = true; this.load(); }

    if (this.interactive) this.bind();
  };

  View.prototype.makeGizmo = function () {
    var g = new THREE.Group(), s = new THREE.Scene();
    function axis(dir, col) {
      var m = new THREE.LineBasicMaterial({ color: lin(col), toneMapped: false });
      g.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(), dir.clone()]), m));
    }
    function label(txt, pos, col) {
      var cv = document.createElement('canvas'); cv.width = cv.height = 64;
      var x = cv.getContext('2d'); x.fillStyle = col; x.font = '600 34px "IBM Plex Mono", monospace';
      x.textAlign = 'center'; x.textBaseline = 'middle'; x.fillText(txt, 32, 34);
      var sp = new THREE.Sprite(new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(cv), toneMapped: false, depthTest: false }));
      sp.position.copy(pos); sp.scale.setScalar(0.55); g.add(sp);
    }
    axis(new THREE.Vector3(1, 0, 0), '#A4ABAB'); label('X', new THREE.Vector3(1.32, 0, 0), '#A4ABAB');
    axis(new THREE.Vector3(0, 1, 0), '#FFFFFF'); label('Y', new THREE.Vector3(0, 1.32, 0), '#FFFFFF');
    axis(new THREE.Vector3(0, 0, 1), '#00A3AB'); label('Z', new THREE.Vector3(0, 0, 1.32), '#3AB3B9');
    s.add(g);
    this.gz = { scene: s, group: g, cam: new THREE.OrthographicCamera(-1.7, 1.7, 1.7, -1.7, 0.1, 10) };
    this.gz.cam.position.set(0, 0, 4);
  };

  /* lens outline drawn in pixel space on top of the model */
  View.prototype.makeLensRing = function () {
    var s = new THREE.Scene(), pts = [], seg = [];
    for (var i = 0; i <= 128; i++) { var a = i / 128 * Math.PI * 2; pts.push(new THREE.Vector3(Math.cos(a), Math.sin(a), 0)); }
    var m = new THREE.LineBasicMaterial({ color: lin('#00A3AB'), toneMapped: false, transparent: true, opacity: 0 });
    var loop = new THREE.LineLoop(new THREE.BufferGeometry().setFromPoints(pts), m);
    var t = 0.07;
    [[1 - t, 0, 1 + t, 0], [-1 - t, 0, -1 + t, 0], [0, 1 - t, 0, 1 + t], [0, -1 - t, 0, -1 + t]].forEach(function (q) {
      seg.push(new THREE.Vector3(q[0], q[1], 0), new THREE.Vector3(q[2], q[3], 0));
    });
    var ticks = new THREE.LineSegments(new THREE.BufferGeometry().setFromPoints(seg), m);
    var grp = new THREE.Group(); grp.add(loop, ticks); s.add(grp);
    this.lensUI = { scene: s, grp: grp, mat: m, cam: new THREE.OrthographicCamera(0, 1, 1, 0, -1, 1) };
  };

  View.prototype.resize = function () {
    var r = this.c.getBoundingClientRect();
    var w = Math.max(1, r.width), h = Math.max(1, r.height);
    var d = this.dpr, px = w * h * d * d;
    var cap = this.own ? 3200000 : 1400000;
    if (px > cap) d = Math.sqrt(cap / (w * h));
    this.cssW = w; this.cssH = h;
    var W = Math.round(w * d), H = Math.round(h * d);
    if (this.own && this.R) { this.R.setSize(W, H, false); }
    else { this.c.width = W; this.c.height = H; }
    this.pxScale = d;
    this.cam.aspect = w / h; this.cam.updateProjectionMatrix();
    this.fitCam();
    this.dirty = true;
  };

  View.prototype.fitCam = function () {
    var r = this.radius || 0.75;
    var vf = THREE.MathUtils.degToRad(this.cam.fov);
    var hf = 2 * Math.atan(Math.tan(vf / 2) * this.cam.aspect);
    this.dist0 = (r / Math.sin(Math.min(vf, hf) / 2)) * (this.o.fit || 1.06);
  };

  View.prototype.load = function () {
    var self = this;
    if (this.loading || this.ready || this.dead) return;
    if (!G.supported) { this.emit({ status: 'nogl' }); return; }
    if (!this.o.src) { this.emit({ status: 'error', reason: 'missing' }); return; }
    this.loading = true;
    this.emit({ status: 'loading', progress: 0 });
    load(this.o.src, this.o.priority, function (p) {
      if (!self.dead) self.emit({ status: 'loading', progress: p });
    }).then(function (g) {
      if (self.dead) return;
      var run = function () {
        if (self.dead) return;
        try {
          if (self.own && !self.R) { self.R = makeRenderer(self.c); self.resize(); }
          self.build(g);
        } catch (e) { self.emit({ status: 'error', reason: String(e) }); return; }
        self.ready = true; self.dirty = true;
        self.emit({ status: 'ready', info: self.info });
        start();
      };
      if ((self.o.priority || 0) <= 0) run(); else queueBuild(run);
    }, function (err) {
      if (!self.dead) self.emit({ status: 'error', reason: String(err && err.message || err) });
    });
  };

  View.prototype.build = function (gltf) {
    var o = this.o, self = this;
    var root = gltf.scene.clone(true);
    root.updateMatrixWorld(true);
    var box = new THREE.Box3().setFromObject(root);
    var size = box.getSize(new THREE.Vector3()), center = box.getCenter(new THREE.Vector3());
    var maxD = Math.max(size.x, size.y, size.z) || 1;
    root.position.sub(center);
    var norm = new THREE.Group(); norm.scale.setScalar(1 / maxD); norm.add(root);
    this.pivot = new THREE.Group(); this.pivot.add(norm);
    this.scene.add(this.pivot);
    var env = (this.own ? this.R : sharedRenderer()).__env;
    if (env) this.scene.environment = env;
    this.pivot.updateMatrixWorld(true);
    this.radius = 0.5 * Math.sqrt(size.x * size.x + size.y * size.y + size.z * size.z) / maxD;
    this.fitCam();

    var meshes = [];
    root.traverse(function (n) { if (n.isMesh) meshes.push(n); });

    var policy = o.surface || 'auto';
    var neutral = policy === 'neutral' || (policy === 'auto' && meshes.every(function (m) {
      var mm = Array.isArray(m.material) ? m.material : [m.material]; return mm.every(unsuitable);
    }));
    var pal = o.palette || ['#D3D7D7', '#2B3031', '#8E9595'];

    function compOf(m) {
      var p = m.parent;
      return (p && p !== root && p.type === 'Group' && p.children.length > 1 && p.children.every(function (c) { return c.isMesh; })) ? p : m;
    }
    var cvol = new Map();
    meshes.forEach(function (m) {
      var n = compOf(m);
      if (!cvol.has(n)) { var s = new THREE.Box3().setFromObject(n).getSize(new THREE.Vector3()); cvol.set(n, Math.max(1e-12, s.x * s.y * s.z)); }
    });
    var cl = Array.from(cvol.keys()).sort(function (a, b) { return cvol.get(b) - cvol.get(a); });
    var big = cl.length ? cvol.get(cl[0]) : 1, crank = new Map();
    cl.forEach(function (n, i) { crank.set(n, i === 0 ? 0 : (cvol.get(n) < big * 0.004 ? 2 : 1)); });

    var whole = new THREE.Box3().setFromObject(this.pivot).getCenter(new THREE.Vector3());
    var tris = 0;
    meshes.forEach(function (m) { tris += triCount(m.geometry); });
    var faintOp = o.meshLines === false ? 0 : tris < 12000 ? 0.07 : tris < 30000 ? 0.04 : 0;
    var useLens = this.lens;
    this.parts = [];

    // shared materials per view (far fewer state changes than one per mesh)
    var ghostMat = new THREE.MeshBasicMaterial({ colorWrite: false, clippingPlanes: [this.planeW], polygonOffset: true, polygonOffsetFactor: 1, polygonOffsetUnits: 1, side: THREE.DoubleSide });
    var lineMat = new THREE.LineBasicMaterial({ color: lin(o.lineColor || '#FFFFFF'), transparent: true, opacity: 0.92, toneMapped: false, clippingPlanes: [this.planeW], depthWrite: false });
    var faintMat = new THREE.LineBasicMaterial({ color: lin(o.lineColor || '#FFFFFF'), transparent: true, opacity: faintOp, toneMapped: false, clippingPlanes: [this.planeW], depthWrite: false });
    var neutralMats = pal.map(function (col, r) {
      var metal = r === 2;
      return new THREE.MeshPhysicalMaterial({ color: lin(col), roughness: metal ? 0.28 : 0.46, metalness: metal ? 0.85 : 0.0, clearcoat: metal ? 0 : 0.35, clearcoatRoughness: 0.35, side: THREE.DoubleSide, clippingPlanes: [self.planeS] });
    });
    if (useLens) {
      lensify(ghostMat, this.uW); lensify(lineMat, this.uW); lensify(faintMat, this.uW);
      neutralMats.forEach(function (m) { lensify(m, self.uS); });
    }
    var origCache = new Map();

    meshes.forEach(function (m) {
      var rank = crank.get(compOf(m));
      var mats = Array.isArray(m.material) ? m.material : [m.material];
      var surf = mats.map(function (mm) {
        if (neutral || unsuitable(mm)) return neutralMats[Math.min(rank, neutralMats.length - 1)];
        if (!origCache.has(mm)) {
          var nm = mm.clone(); nm.clippingPlanes = [self.planeS]; nm.side = THREE.DoubleSide;
          if (useLens) lensify(nm, self.uS);
          origCache.set(mm, nm);
        }
        return origCache.get(mm);
      });
      m.material = surf.length === 1 ? surf[0] : surf;

      var ghost = new THREE.Mesh(m.geometry, ghostMat); ghost.renderOrder = 1; m.add(ghost);
      var edges = new THREE.LineSegments(edgesFor(m.geometry, o.edgeAngle || 22), lineMat);
      edges.renderOrder = 3; m.add(edges);
      if (faintOp > 0) { var wf = new THREE.LineSegments(wireFor(m.geometry), faintMat); wf.renderOrder = 2; m.add(wf); }
    });

    cl.forEach(function (n) {
      var c = new THREE.Box3().setFromObject(n).getCenter(new THREE.Vector3());
      var dir = c.clone().sub(whole);
      var p = n.parent;
      var a = p.worldToLocal(c.clone()), b = p.worldToLocal(c.clone().add(dir.clone().multiplyScalar(0.95)));
      self.parts.push({ m: n, base: n.position.clone(), d: b.sub(a), len: dir.length() });
    });

    var movable = this.parts.filter(function (pp) { return pp.len > 0.03; }).length;
    this.explodable = o.explode === false ? false : (cl.length >= 2 && movable >= 1);
    if (!this.explodable && this.mode === 'exploded') { this.mode = 'surface'; this.explode = 0; }

    this.info = { parts: cl.length, tris: tris, explodable: this.explodable, bounds: [size.x, size.y, size.z], neutral: neutral };
    this.applyReveal(); this.applyExplode();
  };

  View.prototype.applyReveal = function () {
    var y0 = this.pivot ? this.pivot.position.y : 0;
    var r = this.reveal, h = lerp(-0.95, 0.95, r) + y0;
    this.planeS.constant = h; this.planeW.constant = -h;
    this.ring.position.y = h;
    this.ring.material.opacity = (r > 0.001 && r < 0.999) ? 0.9 * Math.sin(r * Math.PI) : 0;
  };
  View.prototype.applyExplode = function () {
    var e = ease(this.explode);
    if (this.parts) this.parts.forEach(function (p) { p.m.position.copy(p.base).addScaledVector(p.d, e); });
  };

  View.prototype.tween = function (key, to, ms) {
    if (reduced) ms = 0;
    this.tw[key] = { from: this[key], to: to, t0: performance.now(), ms: ms };
    this.dirty = true; start();
  };
  View.prototype.setMode = function (mode) {
    if (mode === 'exploded' && !this.explodable && this.ready) mode = 'surface';
    this.mode = mode;
    var rv = mode === 'wire' ? 0 : 1, ex = mode === 'exploded' ? 1 : 0;
    if (rv !== this.reveal) this.tween('reveal', rv, 1000);
    if (ex !== this.explode) this.tween('explode', ex, 950);
  };
  View.prototype.setActive = function (on) { this.active = !!on; this.dirty = true; start(); };
  View.prototype.resetView = function () { this.resetting = true; this.zoomT = 1; this.panXT = 0; this.panYT = 0; this.vy = this.vp = 0; this.dirty = true; start(); };
  View.prototype.zoomBy = function (f) { this.zoomT = clamp(this.zoomT * f, 0.6, 2.6); this.dirty = true; start(); };

  /* ---------- interaction ---------- */
  View.prototype.bind = function () {
    var self = this, c = this.c;
    function pinchDist() {
      var k = Object.keys(self.pointers); if (k.length < 2) return 0;
      var a = self.pointers[k[0]], b = self.pointers[k[1]];
      return Math.hypot(a.x - b.x, a.y - b.y);
    }
    function mid() {
      var k = Object.keys(self.pointers), a = self.pointers[k[0]], b = self.pointers[k[1]];
      return { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
    }
    function panBy(dx, dy) {
      // screen pixels → world units at the model's distance
      var d = self.dist0 / self.zoom, h = 2 * d * Math.tan(THREE.MathUtils.degToRad(self.cam.fov) / 2);
      var k = h / Math.max(1, self.cssH || 1);
      self.panXT = clamp(self.panXT - dx * k, -0.8, 0.8); self.panYT = clamp(self.panYT + dy * k, -0.8, 0.8);
    }
    function pdown(e) {
      if (!self.ready) return;
      self.pointers[e.pointerId] = { x: e.clientX, y: e.clientY };
      self.engaged = true; self.lastInteract = performance.now(); self.resetting = false;
      if (Object.keys(self.pointers).length === 1) {
        self.dragging = true; self.px = e.clientX; self.py = e.clientY;
        self.panning = e.button === 1 || e.button === 2 || e.shiftKey;
      } else { self.pinch0 = pinchDist(); self.zoom0 = self.zoomT; self.mid = mid(); self.panning = false; }
      try { c.setPointerCapture(e.pointerId); } catch (er) {}
      start();
    }
    function pmove(e) {
      if (self.lens && e.pointerType === 'mouse') {
        var rc = c.getBoundingClientRect();
        self.lxT = e.clientX - rc.left; self.lyT = e.clientY - rc.top;
        if (self.lr < 1) { self.lx = self.lxT; self.ly = self.lyT; }
        self.lensOn = true; start();
      }
      if (!self.pointers[e.pointerId]) return;
      self.pointers[e.pointerId] = { x: e.clientX, y: e.clientY };
      if (Object.keys(self.pointers).length >= 2 && self.pinch0) {
        self.zoomT = clamp(self.zoom0 * pinchDist() / self.pinch0, 0.6, 2.6);
        var m = mid(); panBy(m.x - self.mid.x, m.y - self.mid.y); self.mid = m;
      } else if (self.dragging) {
        var dx = e.clientX - self.px, dy = e.clientY - self.py;
        self.px = e.clientX; self.py = e.clientY;
        if (self.panning) { panBy(dx, dy); }
        else {
          self.yaw += dx * 0.009; self.pitch = clamp(self.pitch + dy * 0.006, -0.9, 1.15);
          self.vy = dx * 0.006; self.vp = dy * 0.004;
        }
      }
      self.lastInteract = performance.now(); self.dirty = true; start();
    }
    function pup(e) {
      delete self.pointers[e.pointerId];
      if (!Object.keys(self.pointers).length) self.dragging = false;
      self.pinch0 = 0; start();
    }
    function wheel(e) {
      if (!self.ready || !(self.engaged || e.ctrlKey)) return;
      e.preventDefault();
      self.zoomT = clamp(self.zoomT * Math.exp(-e.deltaY * 0.0015), 0.6, 2.6);
      self.lastInteract = performance.now(); start();
    }
    function leave() { if (!self.dragging) self.engaged = false; self.lensOn = false; start(); }
    function dbl() { self.resetView(); }
    c.addEventListener('pointerdown', pdown);
    c.addEventListener('pointermove', pmove, { passive: true });
    c.addEventListener('pointerup', pup);
    c.addEventListener('pointercancel', pup);
    c.addEventListener('pointerleave', leave);
    c.addEventListener('wheel', wheel, { passive: false });
    var ctx = function (e) { e.preventDefault(); };
    c.addEventListener('contextmenu', ctx);
    c.addEventListener('dblclick', dbl);
    this.unbind = function () {
      c.removeEventListener('pointerdown', pdown); c.removeEventListener('pointermove', pmove);
      c.removeEventListener('pointerup', pup); c.removeEventListener('pointercancel', pup);
      c.removeEventListener('pointerleave', leave); c.removeEventListener('wheel', wheel);
      c.removeEventListener('dblclick', dbl); c.removeEventListener('contextmenu', ctx);
    };
  };

  /* advance one frame; returns true while anything is still moving */
  View.prototype.update = function (dt, now) {
    var moving = false, k, A = 0.0005;
    for (k in this.tw) {
      var t = this.tw[k], u = t.ms ? clamp((now - t.t0) / t.ms, 0, 1) : 1;
      this[k] = lerp(t.from, t.to, k === 'explode' ? u : ease(u));
      if (u >= 1) { this[k] = t.to; delete this.tw[k]; }
      moving = true;
    }
    if (moving) this.applyExplode();

    if (!this.dragging && (this.vy || this.vp)) {
      this.yaw += this.vy; this.pitch = clamp(this.pitch + this.vp, -0.9, 1.15);
      this.vy *= 0.86; this.vp *= 0.84;
      if (Math.abs(this.vy) < 1e-5) this.vy = 0;
      if (Math.abs(this.vp) < 1e-5) this.vp = 0;
      moving = true;
    }
    if (this.dragging) moving = true;
    if (this.resetting) {
      var tw = 2 * Math.PI, dy = ((this.yaw0 - this.yaw) % tw + tw * 1.5) % tw - Math.PI;
      this.yaw += dy * Math.min(1, dt * 5); this.pitch = lerp(this.pitch, this.pitch0, Math.min(1, dt * 5));
      if (Math.abs(dy) < 0.002 && Math.abs(this.pitch - this.pitch0) < 0.002) this.resetting = false;
      moving = true;
    }
    var z = damp(this.zoom, this.zoomT, 8, dt);
    if (Math.abs(z - this.zoomT) > A) moving = true;
    this.zoom = Math.abs(z - this.zoomT) < A ? this.zoomT : z;

    var pxn = damp(this.panX, this.panXT, 12, dt), pyn = damp(this.panY, this.panYT, 12, dt);
    if (Math.abs(pxn - this.panXT) > 1e-4 || Math.abs(pyn - this.panYT) > 1e-4) moving = true;
    this.panX = pxn; this.panY = pyn;

    if (this.lens) {
      var lt = (this.lensOn && !this.dragging) ? (this.o.lensR || 110) : 0;
      var nr = damp(this.lr, lt, reduced ? 60 : 10, dt);
      if (Math.abs(nr - lt) > 0.05) moving = true;
      this.lr = Math.abs(nr - lt) < 0.05 ? lt : nr;
      if (this.lxT != null) {
        var nx = damp(this.lx, this.lxT, 16, dt), ny = damp(this.ly, this.lyT, 16, dt);
        if (Math.abs(nx - this.lxT) > 0.05 || Math.abs(ny - this.lyT) > 0.05) moving = true;
        this.lx = nx; this.ly = ny;
      }
    }

    if (this.pivot) {
      this.pivot.rotation.set(this.pitch, this.yaw, 0, 'XYZ');
      this.pivot.position.y = 0;
    }
    var d = this.dist0 * (1 + 0.42 * ease(this.explode)) / this.zoom;
    this.cam.position.set(this.panX, this.panY + d * 0.06, d);
    this.cam.lookAt(this.panX, this.panY, 0);
    return moving;
  };

  View.prototype.setLensUniforms = function (H) {
    var on = this.lens && this.lr > 1 && !this.tw.reveal && this.pivot;
    if (!on) { this.uS.value.z = 0; this.uW.value.z = 0; this.applyReveal(); return false; }
    var px = this.pxScale, x = this.lx * px, y = H - this.ly * px, r = this.lr * px;
    var surfaceOutside = this.reveal > 0.5;
    this.uS.value.set(x, y, r, surfaceOutside ? 0 : 1);
    this.uW.value.set(x, y, r, surfaceOutside ? 1 : 0);
    // with the lens open both states are drawn, so the scan clipping steps aside
    this.planeS.constant = 10; this.planeW.constant = 10; this.ring.material.opacity = 0;
    return true;
  };

  View.prototype.draw = function () {
    var R, w, h, y = 0;
    if (this.own) {
      R = this.R; if (!R) return;
      w = R.domElement.width; h = R.domElement.height;
      R.setScissorTest(false);
      R.setViewport(0, 0, w, h);
    } else {
      R = sharedRenderer(); w = this.c.width; h = this.c.height;
      if (w > R.__w || h > R.__h) { R.__w = Math.max(R.__w, w); R.__h = Math.max(R.__h, h); R.setSize(R.__w, R.__h, false); }
      y = R.__h - h;
      R.setScissorTest(true);
      R.setViewport(0, y, w, h); R.setScissor(0, y, w, h);
    }
    if (w < 2 || h < 2) return;
    R.setClearColor(0x000000, 0); R.clear(true, true, true);
    var lensOn = this.setLensUniforms(h);
    R.render(this.scene, this.cam);

    if (lensOn && this.lensUI) {
      var L = this.lensUI, px = this.pxScale;
      L.cam.left = 0; L.cam.right = w; L.cam.top = h; L.cam.bottom = 0; L.cam.updateProjectionMatrix();
      L.grp.position.set(this.lx * px, h - this.ly * px, 0);
      L.grp.scale.setScalar(this.lr * px);
      L.mat.opacity = clamp(this.lr / (this.o.lensR || 110), 0, 1);
      R.clearDepth(); R.render(L.scene, L.cam);
    }
    if (this.gz && this.pivot) {
      var s = this.pxScale, gs = Math.round(78 * s), off = Math.round(10 * s);
      R.setScissorTest(true);
      R.setViewport(off, y + off, gs, gs); R.setScissor(off, y + off, gs, gs);
      R.clearDepth();
      this.gz.group.quaternion.copy(this.pivot.quaternion);
      R.render(this.gz.scene, this.gz.cam);
      R.setScissorTest(!this.own);
    }
    if (!this.own) {
      this.ctx.clearRect(0, 0, w, h);
      this.ctx.drawImage(R.domElement, 0, y, w, h, 0, 0, w, h);
    }
    this.dirty = false;
  };

  View.prototype.dispose = function () {
    this.dead = true;
    if (this.ro) this.ro.disconnect();
    if (this.ioNear) this.ioNear.disconnect();
    if (this.ioVis) this.ioVis.disconnect();
    if (this.unbind) this.unbind();
    if (this.R) { try { this.R.dispose(); this.R.forceContextLoss(); } catch (e) {} this.R = null; }
    var i = views.indexOf(this); if (i >= 0) views.splice(i, 1);
  };

  /* ---------- loop: only runs while some visible view is changing ---------- */
  function frame(t) {
    raf = 0;
    var dt = Math.min(0.05, lastT ? (t - lastT) / 1000 : 0.016); lastT = t;
    if (document.hidden) return;
    var again = false, sharedDraws = 0;
    for (var i = 0; i < views.length; i++) {
      var v = views[i];
      if (!v.ready || !v.visible) continue;
      var moving = v.update(dt, t);
      if (moving || v.dirty) {
        // shared views copy pixels; cap them per frame so one frame never stalls
        if (!v.own && sharedDraws >= 3 && !v.dragging) { v.dirty = true; again = true; continue; }
        v.draw(); if (!v.own) sharedDraws++;
      }
      if (moving || v.dirty) again = true;
    }
    if (again) raf = requestAnimationFrame(frame); else lastT = 0;
  }
  function start() { if (!raf) raf = requestAnimationFrame(frame); }
  document.addEventListener('visibilitychange', function () { if (!document.hidden) { lastT = 0; start(); } });
  window.addEventListener('pointermove', function (e) {
    pointer.x = (e.clientX / Math.max(1, window.innerWidth)) * 2 - 1;
    pointer.y = (e.clientY / Math.max(1, window.innerHeight)) * 2 - 1;
  }, { passive: true });

  /* image paths bound from data resolve through the canvas runtime's file map */
  var urlCache = {};
  G.url = function (path) {
    if (!path) return '';
    if (urlCache[path]) return urlCache[path];
    var out = path;
    try {
      var f = typeof window.__dcLookup === 'function' ? window.__dcLookup(path) : null;
      if (f && f.bytes) out = URL.createObjectURL(new Blob([f.bytes], { type: f.mime }));
      else if (window.__dcPartBlobs && window.__dcPartBlobs[path]) out = URL.createObjectURL(window.__dcPartBlobs[path]);
    } catch (e) { out = path; }
    urlCache[path] = out;
    return out;
  };

  G.mount = function (canvas, opts) {
    var v = new View(canvas, opts || {});
    views.push(v);
    if (!G.supported) setTimeout(function () { v.emit({ status: 'nogl' }); }, 0);
    return {
      setMode: function (m) { v.setMode(m); },
      setActive: function (on) { v.setActive(on); },
      reset: function () { v.resetView(); },
      zoomBy: function (f) { v.zoomBy(f); },
      dispose: function () { v.dispose(); },
      view: v
    };
  };
})();

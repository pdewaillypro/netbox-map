/* NetBox Map — Topology Renderer Module */
/* Node view (circles) and Stencil view (device cards with centered ports) */

(function(App) {
    'use strict';

    // Natural sort: "Gi0/2" before "Gi0/10" (not lexicographic)
    function naturalCompare(a, b) {
        return (a || '').localeCompare(b || '', undefined, { numeric: true, sensitivity: 'base' });
    }

    var CARD_W = 200;
    // Patch panels drawn as two columns (front ports | rear ports): wider card.
    var PANEL_W = 320;
    var PANEL_GAP = 14;       // gap between the two columns, where the internal links are drawn

    function cardW(d) { return (d && d._w) || CARD_W; }

    function isFrontId(id) { return String(id).indexOf('fp-') === 0; }
    var HEADER_H = 38;
    var PORT_H = 24;          // height of each port container
    var PORT_GAP = 3;         // gap between port containers
    var PORT_TEXT_PAD = 12;   // text padding inside port container
    var CARD_PAD = 10;
    var LAYER_GAP_X = 480;
    var NODE_GAP_Y = 55;

    // Compute layer assignment from actual cable connections via BFS.
    // Devices with fewest connections or no "upstream" are placed left (layer 0).
    // Falls back to role-based hints if available.
    function computeLayers(nodeData, edgeData) {
        var nodeIds = {};
        nodeData.forEach(function(n) { nodeIds[n.id] = n; });

        // Build adjacency + connection counts
        var adj = {};
        var degree = {};
        nodeData.forEach(function(n) { adj[n.id] = []; degree[n.id] = 0; });
        edgeData.forEach(function(e) {
            var s = typeof e.source === 'object' ? e.source.id : e.source;
            var t = typeof e.target === 'object' ? e.target.id : e.target;
            if (adj[s] && adj[t]) {
                adj[s].push(t);
                adj[t].push(s);
                degree[s]++;
                degree[t]++;
            }
        });

        // Find root candidates: devices with fewest connections (edge devices)
        // or use role hints if they match common patterns
        var ROLE_HINTS = {
            'firewall': 0, 'fw': 0,
            'router': 1, 'rtr': 1, 'edge': 1,
            'core': 2,
            'distribution': 3, 'dist': 3, 'aggregation': 3,
            'access': 4, 'leaf': 4,
            'server': 5, 'host': 5, 'compute': 5, 'storage': 5,
            'patch': 3, 'panel': 3,
        };

        function roleHint(slug) {
            if (!slug) return -1;
            slug = slug.toLowerCase();
            for (var k in ROLE_HINTS) {
                if (slug.indexOf(k) !== -1) return ROLE_HINTS[k];
            }
            return -1;
        }

        // Check if any role hints match
        var hasHints = nodeData.some(function(n) { return roleHint(n.role_slug) >= 0; });

        if (hasHints) {
            // Use role hints — group by hint value, unmatched roles get assigned
            // based on their connections to hinted devices
            var layers = {};
            var unassigned = [];
            nodeData.forEach(function(n) {
                var hint = roleHint(n.role_slug);
                if (hint >= 0) {
                    if (!layers[hint]) layers[hint] = [];
                    layers[hint].push(n);
                    n._layer = hint;
                } else {
                    unassigned.push(n);
                }
            });

            // Assign unmatched devices based on neighbors' average layer
            unassigned.forEach(function(n) {
                var neighbors = adj[n.id] || [];
                var sum = 0, count = 0;
                neighbors.forEach(function(nid) {
                    var nb = nodeIds[nid];
                    if (nb && nb._layer !== undefined) { sum += nb._layer; count++; }
                });
                var layer = count > 0 ? Math.round(sum / count) : 5;
                n._layer = layer;
                if (!layers[layer]) layers[layer] = [];
                layers[layer].push(n);
            });

            return layers;
        }

        // No role hints — use pure BFS from lowest-degree nodes
        var sorted = nodeData.slice().sort(function(a, b) {
            return (degree[a.id] || 0) - (degree[b.id] || 0);
        });

        // BFS from the node with fewest connections
        var visited = {};
        var layers = {};
        var queue = [];

        // Start from lowest-degree node
        if (sorted.length > 0) {
            var root = sorted[0];
            queue.push({ node: root, level: 0 });
            visited[root.id] = true;
        }

        while (queue.length > 0) {
            var item = queue.shift();
            var lvl = item.level;
            if (!layers[lvl]) layers[lvl] = [];
            layers[lvl].push(item.node);
            item.node._layer = lvl;

            (adj[item.node.id] || []).forEach(function(nid) {
                if (!visited[nid] && nodeIds[nid]) {
                    visited[nid] = true;
                    queue.push({ node: nodeIds[nid], level: lvl + 1 });
                }
            });
        }

        // Handle disconnected nodes
        nodeData.forEach(function(n) {
            if (!visited[n.id]) {
                var maxLayer = Object.keys(layers).length;
                if (!layers[maxLayer]) layers[maxLayer] = [];
                layers[maxLayer].push(n);
                n._layer = maxLayer;
            }
        });

        return layers;
    }

    /**
     * Topological layering for directed dependency graphs.
     * Edge convention: source DEPENDS ON target (source→target arrow).
     * Providers (no outgoing deps) go to layer 0 (leftmost).
     * Consumers go to higher layers (rightward).
     * Uses longest-path algorithm to ensure connected nodes are never
     * in the same column.
     */
    function computeAppLayers(appNodes, depEdges) {
        var nodeIds = {};
        appNodes.forEach(function(n) { nodeIds[n.id] = n; });

        // outEdges: what each node depends on (targets)
        var outEdges = {};
        appNodes.forEach(function(n) { outEdges[n.id] = []; });
        depEdges.forEach(function(e) {
            var s = typeof e.source === 'object' ? e.source.id : e.source;
            var t = typeof e.target === 'object' ? e.target.id : e.target;
            if (outEdges[s] && nodeIds[t]) outEdges[s].push(t);
        });

        // Longest-path layer assignment (recursive with cycle protection)
        var layerOf = {};
        var computing = {};

        function getLayer(id) {
            if (layerOf[id] !== undefined) return layerOf[id];
            if (computing[id]) return 0; // cycle
            computing[id] = true;
            var targets = outEdges[id] || [];
            var maxL = -1;
            targets.forEach(function(tid) {
                if (nodeIds[tid]) maxL = Math.max(maxL, getLayer(tid));
            });
            layerOf[id] = maxL + 1; // providers get 0, their dependents get 1+
            delete computing[id];
            return layerOf[id];
        }

        appNodes.forEach(function(n) { getLayer(n.id); });

        // Build layers object
        var layers = {};
        appNodes.forEach(function(n) {
            var lk = layerOf[n.id] || 0;
            n._layer = lk;
            if (!layers[lk]) layers[lk] = [];
            layers[lk].push(n);
        });

        return layers;
    }

    function Renderer(state, events) {
        this.state = state;
        this.events = events;
        this.svg = null;
        this.g = null;
        this.zoom = null;
        this.simulation = null;
        this.nodeElements = null;
        this.edgeElements = null;
        this.width = 0;
        this.height = 0;
        this._stencilNodeData = null;
        this._stencilPortPos = null;
        this._simulationActive = false;
        this._simulationSourceId = null;
        this._simulationImpacted = new Set();
    }

    Renderer.prototype.init = function() {
        var self = this;
        this.svg = d3.select('#topology-svg');
        this._updateSize();
        this.g = this.svg.append('g');
        this.g.append('g').attr('class', 'edge-layer');       // all edges (cables + app) — behind cards
        this.g.append('g').attr('class', 'node-layer');       // device cards
        this.g.append('g').attr('class', 'overlay-node-layer'); // app cards — above device cards
        this.g.append('g').attr('class', 'highlight-layer');  // hover-highlighted edges — topmost

        this.zoom = d3.zoom().scaleExtent([0.02, 5])
            .on('zoom', function(ev) { self.g.attr('transform', ev.transform); });
        this.svg.call(this.zoom);
        this.svg.on('dblclick.zoom', null);
        this.svg.on('click', function(ev) {
            if (ev.target === self.svg.node()) {
                self._deselectAll(); self.events.emit('node:deselect');
                // A plain click on the background also empties the multi-selection
                if (!ev.shiftKey && !ev.ctrlKey && !ev.metaKey && self._multiSel().size) {
                    self._multiSel().clear(); self._applyMultiSelection();
                }
            }
        });

        // Shift+drag on the background draws a selection rectangle instead of panning
        this.zoom.filter(function(ev) {
            if (ev.type === 'mousedown' && ev.shiftKey) return false;
            return (!ev.ctrlKey || ev.type === 'wheel') && !ev.button;
        });
        this._initMultiSelect();

        // Arrow markers — sleek chevron style, dynamically created per color
        var defs = this.svg.append('defs');
        this._arrowDefs = defs;
        this._arrowColors = {};
        this._ensureArrow = function(hex) {
            hex = hex.replace('#', '');
            if (this._arrowColors[hex]) return;
            this._arrowColors[hex] = true;
            this._arrowDefs.append('marker').attr('id', 'arrow-' + hex)
                .attr('viewBox', '0 -4 8 8').attr('refX', 8).attr('refY', 0)
                .attr('markerWidth', 8).attr('markerHeight', 8).attr('orient', 'auto')
                .append('path').attr('d', 'M0,-3L8,0L0,3').attr('fill', 'none')
                .attr('stroke', '#' + hex).attr('stroke-width', 1.5)
                .attr('stroke-linejoin', 'round');
        };
        // Pre-create common ones
        var self2 = this;
        ['e74c3c','e67e22','f39c12','3498db','6c757d','5a6080'].forEach(function(hex) { self2._ensureArrow(hex); });
    };

    /* ---- Multi-selection: Ctrl/Cmd+click, Shift+drag lasso, drag together, arrow keys ---- */

    /* ---- Placement grid (shown while snap-to-grid is on): minor/major lines and rulers ---- */

    Renderer.prototype._drawGrid = function(nodeData) {
        this.g.selectAll('.topo-grid').remove();
        if (!this.state.snapToGrid || !nodeData || !nodeData.length) return;
        var gs = this.state.gridSize || 20, major = gs * 5;
        var x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
        nodeData.forEach(function(n) {
            x0 = Math.min(x0, n.x); y0 = Math.min(y0, n.y);
            x1 = Math.max(x1, n.x + cardW(n)); y1 = Math.max(y1, n.y + (n._cardH || 60));
        });
        var nx0 = x0, ny0 = y0;   // top-left of the cards, where the rulers go
        var pad = major * 4;
        x0 = Math.floor((x0 - pad) / major) * major; y0 = Math.floor((y0 - pad) / major) * major;
        x1 = Math.ceil((x1 + pad) / major) * major; y1 = Math.ceil((y1 + pad) / major) * major;

        var grid = this.g.insert('g', ':first-child').attr('class', 'topo-grid');
        var defs = grid.append('defs');
        defs.append('pattern').attr('id', 'topo-grid-minor').attr('patternUnits', 'userSpaceOnUse')
            .attr('width', gs).attr('height', gs)
            .append('path').attr('d', 'M' + gs + ',0 L0,0 0,' + gs).attr('class', 'topo-grid-minor');
        var mj = defs.append('pattern').attr('id', 'topo-grid-major').attr('patternUnits', 'userSpaceOnUse')
            .attr('width', major).attr('height', major);
        mj.append('rect').attr('width', major).attr('height', major).attr('fill', 'url(#topo-grid-minor)');
        mj.append('path').attr('d', 'M' + major + ',0 L0,0 0,' + major).attr('class', 'topo-grid-major');
        grid.append('rect').attr('x', x0).attr('y', y0).attr('width', x1 - x0).attr('height', y1 - y0)
            .attr('fill', 'url(#topo-grid-major)').attr('pointer-events', 'none');
        // Rulers: the major lines numbered in grid steps, along the top and left edges
        var rulerY = ny0 - 8, rulerX = nx0 - 6;
        for (var x = x0; x <= x1; x += major) {
            grid.append('text').attr('class', 'topo-grid-label').attr('x', x + 2).attr('y', rulerY).text(Math.round(x / gs));
        }
        for (var y = y0; y <= y1; y += major) {
            grid.append('text').attr('class', 'topo-grid-label').attr('x', rulerX).attr('y', y + 10)
                .attr('text-anchor', 'end').text(Math.round(y / gs));
        }
    };

    Renderer.prototype._multiSel = function() {
        if (!this.state.multiSelected) this.state.multiSelected = new Set();
        return this.state.multiSelected;
    };

    Renderer.prototype._applyMultiSelection = function() {
        var sel = this._multiSel();
        if (this._stencilCards) {
            this._stencilCards.classed('multi-selected', function(d) { return sel.has(d.id); });
        }
    };

    Renderer.prototype._initMultiSelect = function() {
        var self = this;
        var lasso = null;

        this.svg.on('mousedown.lasso', function(ev) {
            if (!ev.shiftKey || ev.button !== 0 || !self._stencilNodeData) return;
            if (ev.target !== self.svg.node()) return;  // only from the background
            ev.preventDefault();
            var p = d3.pointer(ev, self.g.node());
            lasso = { x0: p[0], y0: p[1], rect: self.g.append('rect').attr('class', 'topo-lasso')
                .attr('x', p[0]).attr('y', p[1]).attr('width', 0).attr('height', 0) };
        });
        d3.select(window).on('mousemove.lasso', function(ev) {
            if (!lasso) return;
            var p = d3.pointer(ev, self.g.node());
            lasso.x1 = p[0]; lasso.y1 = p[1];
            lasso.rect.attr('x', Math.min(lasso.x0, p[0])).attr('y', Math.min(lasso.y0, p[1]))
                .attr('width', Math.abs(p[0] - lasso.x0)).attr('height', Math.abs(p[1] - lasso.y0));
        }).on('mouseup.lasso', function(ev) {
            if (!lasso) return;
            var l = lasso; lasso = null;
            l.rect.remove();
            if (l.x1 === undefined) return;
            var x0 = Math.min(l.x0, l.x1), x1 = Math.max(l.x0, l.x1);
            var y0 = Math.min(l.y0, l.y1), y1 = Math.max(l.y0, l.y1);
            var sel = self._multiSel();
            if (!(ev.ctrlKey || ev.metaKey)) sel.clear();  // Ctrl+Shift+drag adds to the selection
            (self._stencilNodeData || []).forEach(function(nd) {
                var w = cardW(nd), h = nd._cardH || 60;
                if (nd.x < x1 && nd.x + w > x0 && nd.y < y1 && nd.y + h > y0) sel.add(nd.id);
            });
            self._applyMultiSelection();
        });

        document.addEventListener('keydown', function(ev) {
            var tag = (ev.target && ev.target.tagName) || '';
            if (/^(INPUT|TEXTAREA|SELECT)$/.test(tag) || (ev.target && ev.target.isContentEditable)) return;
            var sel = self._multiSel();
            if (!sel.size) return;
            if (ev.key === 'Escape') { sel.clear(); self._applyMultiSelection(); return; }
            var step = (self.state.gridSize || 20) * (ev.shiftKey ? 10 : 1);
            var d = { ArrowLeft: [-step, 0], ArrowRight: [step, 0], ArrowUp: [0, -step], ArrowDown: [0, step] }[ev.key];
            if (d && self._nudgeSelection && self._nudgeSelection(d[0], d[1])) ev.preventDefault();
        });
    };

    Renderer.prototype._updateSize = function() {
        var r = this.svg.node().parentElement.getBoundingClientRect();
        this.width = r.width || 800; this.height = r.height || 600;
        this.svg.attr('width', this.width).attr('height', this.height);
    };

    Renderer.prototype.render = function(nodes, edges, skipFit) {
        this._skipFit = !!skipFit;
        // All modes use _renderStencil — it handles both device and app nodes
        if (this.state.viewMode === 'stencil' || this.state.topologyMode === 'apps') {
            this._renderStencil(nodes, edges);
        } else {
            this._renderNodes(nodes, edges);
        }
    };

    /* ================================================================
       STENCIL VIEW — Centered ports
       ================================================================ */

    Renderer.prototype._renderStencil = function(nodes, edges) {
        var self = this;
        this._updateSize();
        this.g.selectAll('.edge-layer > *, .node-layer > *, .overlay-node-layer > *, .highlight-layer > *').remove();
        if (this.simulation) { this.simulation.stop(); this.simulation = null; }
        if (nodes.length === 0) return;

        var nodeData = nodes.map(function(n) {
            return Object.assign({}, n, { ports: (n.ports || []).slice() });
        });
        var edgeData = edges.map(function(e) { return Object.assign({}, e); });

        // #61 — Hide ports whose other end isn't in the current view.
        // Build a port_id → endpoint device map first, then a set of visible
        // device ids; any port whose remote endpoint isn't visible gets
        // filtered from its card BEFORE card heights are computed, so the
        // cards naturally shrink to fit.
        if (self.state.hideUnconnectedPorts) {
            var _portTargetDev = {};
            edgeData.forEach(function(e) {
                var es = typeof e.source === 'object' ? e.source.id : e.source;
                var et = typeof e.target === 'object' ? e.target.id : e.target;
                if (e.source_port) _portTargetDev[e.source_port] = et;
                if (e.target_port) _portTargetDev[e.target_port] = es;
            });
            var _visibleDevIds = new Set(nodeData.map(function(n) { return n.id; }));
            nodeData.forEach(function(nd) {
                if (nd.node_type === 'application') return;  // apps are filtered differently
                nd.ports = (nd.ports || []).filter(function(p) {
                    return _visibleDevIds.has(_portTargetDev[p.id]);
                });
            });
        }

        // Folded cassettes: on a patch panel, the ports of one module (cassette) collapse into
        // one front and one rear stand-in port, and the cables they carry into one line per
        // bundle (trunk). A click on a folded cassette unfolds it; state.expandedCassettes keeps
        // the unfolded ones ("device-id|bay") across re-renders.
        var foldOn = self.state.orientedPanels !== false && self.state.foldCassettes !== false;
        var expanded = self.state.expandedCassettes || (self.state.expandedCassettes = new Set());
        var portRemap = {};
        if (foldOn) {
            nodeData.forEach(function(nd) {
                var ports = nd.ports || [];
                if (nd.node_type === 'application' || !(nd.passthrough_pairs || []).length || !ports.length) return;
                if (!ports.every(function(p) { return p.port_class === 'front-port' || p.port_class === 'rear-port'; })) return;
                var groups = {};
                ports.forEach(function(p) {
                    if (!p.module || expanded.has(nd.id + '|' + p.module)) return;
                    var g = groups[p.module] || (groups[p.module] = { f: [], r: [] });
                    (p.port_class === 'front-port' ? g.f : g.r).push(p);
                });
                var keys = Object.keys(groups);
                if (!keys.length) return;
                var kept = ports.filter(function(p) { return !p.module || expanded.has(nd.id + '|' + p.module); });
                var pairs = (nd.passthrough_pairs || []).slice();
                keys.sort(naturalCompare).forEach(function(k) {
                    var g = groups[k];
                    var base = 'cas-' + nd.device_id + '-' + k;
                    var vf = null, vr = null;
                    if (g.f.length) {
                        vf = { id: 'fp-' + base, name: k + ' \u00b7 ' + g.f.length + ' front', port_class: 'front-port',
                               module: k, _cassette: k, _members: g.f };
                        g.f.forEach(function(p) { portRemap[p.id] = vf.id; });
                        kept.push(vf);
                    }
                    if (g.r.length) {
                        vr = { id: 'rp-' + base, name: k + ' \u00b7 ' + g.r.length + ' rear', port_class: 'rear-port',
                               module: k, _cassette: k, _members: g.r };
                        g.r.forEach(function(p) { portRemap[p.id] = vr.id; });
                        kept.push(vr);
                    }
                    if (vf && vr) pairs.push({ front: vf.id, rear: vr.id });
                });
                nd.ports = kept;
                nd.passthrough_pairs = pairs;
            });
        }
        if (Object.keys(portRemap).length) {
            var aggByKey = {};
            var folded = [];
            edgeData.forEach(function(e) {
                var sp = portRemap[e.source_port] || e.source_port;
                var tp = portRemap[e.target_port] || e.target_port;
                if (sp === e.source_port && tp === e.target_port) { folded.push(e); return; }
                var key = [sp, tp].sort().join('|') + '|' + (e.bundle_id || '-');
                var a = aggByKey[key];
                if (!a) {
                    var n = Object.keys(aggByKey).length;
                    a = aggByKey[key] = Object.assign({}, e, {
                        id: 'agg-' + n, cable_id: 'agg' + n, source_port: sp, target_port: tp,
                        _members: [],
                    });
                    folded.push(a);
                }
                a._members.push(e);
            });
            Object.keys(aggByKey).forEach(function(key) {
                var a = aggByKey[key];
                var n = a._members.length;
                a._count = n;
                if (n === 1) {
                    // A single fibre into a folded cassette (the other end is unfolded): it keeps
                    // its own label and link, only its end point moves to the folded row.
                    var only = a._members[0];
                    a.cable_label = only.cable_label;
                    a.url = only.url;
                } else if (a.bundle_name) {
                    a.cable_label = a.bundle_name + ' \u00b7 ' + n + ' FO';
                    if (a.bundle_url) a.url = a.bundle_url;
                } else if (n > 1) {
                    a.cable_label = n + ' cables';
                }
                var pn = function(id) {
                    for (var i = 0; i < nodeData.length; i++) {
                        var hit = (nodeData[i].ports || []).find(function(p) { return p.id === id; });
                        if (hit) return hit.name;
                    }
                    return '';
                };
                a.source_port_name = pn(a.source_port);
                a.target_port_name = pn(a.target_port);
            });
            edgeData = folded;
        }

        // Oriented patch panels: a device whose cabled ports are all front/rear ports with a
        // known front↔rear mapping is drawn as two columns — front ports on one side, the rear
        // ports each front port maps to on the other, on the same rows. The front column faces
        // the side most of its neighbours are on (decided below, once positions are known).
        nodeData.forEach(function(nd) {
            nd._w = CARD_W;
            nd._panel = null;
            if (self.state.orientedPanels === false || nd.node_type === 'application') return;
            var pairs = nd.passthrough_pairs || [];
            var ports = nd.ports || [];
            if (!pairs.length || !ports.length) return;
            var onlyPassthrough = ports.every(function(p) {
                return p.port_class === 'front-port' || p.port_class === 'rear-port';
            });
            if (!onlyPassthrough) return;

            var byId = {};
            ports.forEach(function(p) { byId[p.id] = p; });
            var rearsOf = {};
            pairs.forEach(function(m) {
                if (!byId[m.front] || !byId[m.rear]) return;
                var list = rearsOf[m.front] || (rearsOf[m.front] = []);
                if (list.indexOf(byId[m.rear]) < 0) list.push(byId[m.rear]);
            });
            var used = {};
            var rows = [];
            ports.filter(function(p) { return p.port_class === 'front-port'; }).forEach(function(f) {
                var rs = (rearsOf[f.id] || []).filter(function(r) { return !used[r.id]; });
                rs.forEach(function(r) { used[r.id] = true; });
                rs.sort(function(a, b) { return naturalCompare(a.name, b.name); });
                rows.push({ front: f, rears: rs });
            });
            ports.filter(function(p) { return p.port_class === 'rear-port' && !used[p.id]; }).forEach(function(r) {
                rows.push({ front: null, rears: [r] });
            });
            var slots = rows.reduce(function(sum, r) { return sum + Math.max(1, r.rears.length); }, 0);
            // An unfolded cassette gets a heading row (click it to fold the cassette again)
            var headings = {};
            if (foldOn) {
                rows.forEach(function(r) {
                    var p = r.front || r.rears[0];
                    if (p && p.module && !p._cassette) headings[p.module] = true;
                });
            }
            slots += Object.keys(headings).length;
            nd._panel = { rows: rows, slots: slots, frontRight: false, slotOf: {}, headings: headings };
            nd._w = PANEL_W;
        });

        // Compute card heights
        nodeData.forEach(function(nd) {
            if (nd.node_type === 'application') {
                nd.ports = nd.ports || [];
                var portCount = nd.ports.length;
                var appInfoH = 18; // compact info line
                // Section headers are now port rows — no extra height needed
                nd._cardH = HEADER_H + appInfoH + portCount * (PORT_H + PORT_GAP) + CARD_PAD;
                if (portCount === 0) nd._cardH = HEADER_H + appInfoH + CARD_PAD;
                nd._appInfoH = appInfoH;
            } else {
                var portCount = nd._panel ? nd._panel.slots : (nd.ports || []).length;
                nd._cardH = HEADER_H + portCount * (PORT_H + PORT_GAP) + CARD_PAD;
                if (portCount === 0) nd._cardH = HEADER_H + CARD_PAD;
            }
        });

        // ── Layout ──
        var hasApps = nodeData.some(function(n) { return n.node_type === 'application'; });
        var hasDevices = nodeData.some(function(n) { return n.node_type !== 'application'; });

        // Build node lookup
        var nodeById = {};
        nodeData.forEach(function(n) { nodeById[n.id] = n; });

        if (hasApps && typeof dagre !== 'undefined') {
            // ── Dagre layout — ALL nodes (apps + devices) in one graph ──
            // Dagre handles layer assignment, crossing minimization, and coordinate
            // assignment — producing a clean left-to-right hierarchical layout.
            var g = new dagre.graphlib.Graph();
            g.setGraph({
                rankdir: 'LR',
                ranksep: Math.max(LAYER_GAP_X - CARD_W, 120),
                nodesep: 40,
                marginx: 60,
                marginy: 60,
                ranker: 'network-simplex',
            });
            g.setDefaultEdgeLabel(function() { return {}; });

            // Add ALL nodes
            nodeData.forEach(function(n) {
                g.setNode(n.id, { width: cardW(n), height: n._cardH });
            });

            // Add dependency edges (reversed so providers rank left)
            edgeData.forEach(function(e) {
                if (e.edge_type !== 'dependency' && e.edge_type !== 'deployed_on') return;
                var s = typeof e.source === 'object' ? e.source.id : e.source;
                var t = typeof e.target === 'object' ? e.target.id : e.target;
                if (!g.hasNode(s) || !g.hasNode(t)) return;
                if (e.edge_type === 'dependency') {
                    // source DEPENDS ON target → reverse for dagre (target ranked left)
                    g.setEdge(t, s);
                } else {
                    // deployed_on: source=app, target=device → device ranked left
                    g.setEdge(t, s);
                }
            });

            dagre.layout(g);

            // Apply dagre positions (dagre gives center coords → convert to top-left)
            g.nodes().forEach(function(id) {
                var n = nodeById[id];
                var pos = g.node(id);
                if (n && pos) {
                    n.x = pos.x - cardW(n) / 2;
                    n.y = pos.y - (n._cardH || 60) / 2;
                }
            });

        } else {
            // ── Device-only: use existing computeLayers ──
            var layers;
            if (self.state.customHierarchy && Object.keys(self.state.customHierarchy).length > 0) {
                layers = {};
                nodeData.forEach(function(n) {
                    var l = self.state.customHierarchy[n.role_slug];
                    if (l === undefined) l = 99;
                    if (!layers[l]) layers[l] = [];
                    layers[l].push(n);
                    n._layer = l;
                });
            } else {
                layers = computeLayers(nodeData, edgeData);
            }
            var layerKeys = Object.keys(layers).map(Number).sort(function(a, b) { return a - b; });

            // Build adjacency for layout optimization
            var adjList = {};
            nodeData.forEach(function(n) { adjList[n.id] = []; });
            edgeData.forEach(function(e) {
                var s = typeof e.source === 'object' ? e.source.id : e.source;
                var t = typeof e.target === 'object' ? e.target.id : e.target;
                if (adjList[s]) adjList[s].push(t);
                if (adjList[t]) adjList[t].push(s);
            });

            // X coordinates
            layerKeys.forEach(function(lk, col) {
                layers[lk].forEach(function(n) { n.x = 100 + col * LAYER_GAP_X; });
            });

            // Y coordinates: first column alphabetical, rest aligned to connections
            layerKeys.forEach(function(lk, col) {
                var group = layers[lk];
                if (col === 0) {
                    group.sort(function(a, b) { return (a.name || '').localeCompare(b.name || ''); });
                    var curY = 80;
                    group.forEach(function(n) { n.y = curY; curY += n._cardH + NODE_GAP_Y; });
                } else {
                    group.forEach(function(n) {
                        var neighbors = adjList[n.id] || [];
                        var sumY = 0, cntY = 0;
                        neighbors.forEach(function(nid) {
                            var nb = nodeById[nid];
                            if (nb && nb.y !== undefined && nb.x < n.x) {
                                sumY += nb.y + (nb._cardH || 60) / 2;
                                cntY++;
                            }
                        });
                        n._targetY = cntY > 0 ? sumY / cntY - (n._cardH || 60) / 2 : 99999;
                    });
                    group.sort(function(a, b) { return a._targetY - b._targetY; });
                    var placed = [];
                    group.forEach(function(n) {
                        var idealY = n._targetY;
                        if (idealY === 99999) idealY = placed.length > 0
                            ? placed[placed.length - 1].y + placed[placed.length - 1]._cardH + NODE_GAP_Y : 80;
                        var minY = 80;
                        if (placed.length > 0) {
                            var last = placed[placed.length - 1];
                            minY = last.y + last._cardH + NODE_GAP_Y;
                        }
                        n.y = Math.max(idealY, minY);
                        placed.push(n);
                    });
                }
            });
        }

        // Apply saved positions
        var savedLayout = self.state.savedLayout;
        if (savedLayout && typeof savedLayout === 'object') {
            nodeData.forEach(function(n) {
                var saved = savedLayout[n.id];
                if (saved && saved.x !== undefined) { n.x = saved.x; n.y = saved.y; }
            });
        }

        // A cassette was just folded/unfolded: the cards right under that panel move down (or
        // up) by its change in height, so an unfolded panel never ends up behind its neighbour.
        var grow = self._growFrom;
        self._growFrom = null;
        if (grow) {
            var gNode = nodeData.find(function(n) { return n.id === grow.id; });
            if (gNode) {
                var delta = gNode._cardH - grow.h;
                var gx0 = gNode.x, gx1 = gNode.x + cardW(gNode), below = gNode.y + grow.h - 5;
                if (delta) {
                    nodeData.forEach(function(n) {
                        if (n === gNode) return;
                        if (n.x < gx1 && n.x + cardW(n) > gx0 && n.y >= below) n.y += delta;
                    });
                }
                self._raiseId = gNode.id;
            }
        }

        // Snap to grid: every card on the grid, so cards line up with each other, not only
        // the one being dragged.
        if (self.state.snapToGrid) {
            var gsz = self.state.gridSize || 20;
            nodeData.forEach(function(n) {
                n.x = Math.round(n.x / gsz) * gsz;
                n.y = Math.round(n.y / gsz) * gsz;
            });
        }

        // Store positioned node data for external access (save, PDF, etc.)
        this._stencilNodeData = nodeData;

        // Build edge lookup: port_id -> target device id (and port_id -> port at the other end)
        var portTargetDevice = {};
        var portPeer = {};
        edgeData.forEach(function(e) {
            var s = typeof e.source === 'object' ? e.source.id : e.source;
            var t = typeof e.target === 'object' ? e.target.id : e.target;
            if (e.source_port) portTargetDevice[e.source_port] = t;
            if (e.target_port) portTargetDevice[e.target_port] = s;
            if (e.source_port && e.target_port) {
                portPeer[e.source_port] = e.target_port;
                portPeer[e.target_port] = e.source_port;
            }
        });

        // Sort ports on each device card (skip app nodes — their order is set by backend)
        nodeData.forEach(function(nd) {
            if (nd.node_type === 'application') return; // app port order is pre-sorted with section headers
            if (self.state.autoSortPorts) {
                // Smart sort: by target device Y position (minimizes cable crossings)
                nd.ports.sort(function(a, b) {
                    var targetA = portTargetDevice[a.id];
                    var targetB = portTargetDevice[b.id];
                    var devA = targetA ? nodeById[targetA] : null;
                    var devB = targetB ? nodeById[targetB] : null;
                    var yA = devA ? devA.y : 99999;
                    var yB = devB ? devB.y : 99999;
                    if (yA === yB) return naturalCompare(a.name, b.name);
                    return yA - yB;
                });
            } else {
                // Natural sort: Gi0/1, Gi0/2, ... Gi0/10, Gi0/11 (not lexicographic)
                nd.ports.sort(function(a, b) { return naturalCompare(a.name, b.name); });
            }
        });

        // Oriented panels: pick the side of the front column, order the rows, give every port
        // its slot (a front port mapped to two rear ports spans both of their rows).
        nodeData.forEach(function(nd) {
            var P = nd._panel;
            if (!P) return;
            var centre = nd.x + cardW(nd) / 2;
            function meanX(ports) {
                var sum = 0, cnt = 0;
                ports.forEach(function(p) {
                    var other = nodeById[portTargetDevice[p.id]];
                    if (other) { sum += other.x + cardW(other) / 2; cnt++; }
                });
                return cnt ? sum / cnt : null;
            }
            var fronts = [], rears = [];
            P.rows.forEach(function(r) {
                if (r.front) fronts.push(r.front);
                Array.prototype.push.apply(rears, r.rears);
            });
            var fx = meanX(fronts), rx = meanX(rears);
            if (fx !== null && rx !== null) P.frontRight = fx > rx;
            else if (fx !== null) P.frontRight = fx > centre;
            else if (rx !== null) P.frontRight = rx < centre;
            else P.frontRight = false;

            function rowName(r) { return r.front ? r.front.name : (r.rears[0] ? r.rears[0].name : ''); }
            function rowY(r) {
                var best = 99999;
                (r.front ? [r.front] : []).concat(r.rears).forEach(function(p) {
                    var other = nodeById[portTargetDevice[p.id]];
                    if (other && other.y < best) best = other.y;
                });
                return best;
            }
            function rowCas(r) { var p = r.front || r.rears[0]; return (p && p.module) || ''; }
            function byRow(a, b) {
                if (self.state.autoSortPorts) {
                    var ya = rowY(a), yb = rowY(b);
                    if (ya !== yb) return ya - yb;
                }
                if (!a.front !== !b.front) return a.front ? -1 : 1;
                return naturalCompare(rowName(a), rowName(b));
            }
            // Rows stay together per cassette; cassettes are ordered like rows (by where their
            // cables go when auto-sort is on, by name otherwise).
            var groupsOf = {};
            P.rows.forEach(function(r) { (groupsOf[rowCas(r)] = groupsOf[rowCas(r)] || []).push(r); });
            var groupList = Object.keys(groupsOf).map(function(k) {
                var rs = groupsOf[k].sort(byRow);
                return { key: k, rows: rs, y: Math.min.apply(null, rs.map(rowY)) };
            });
            groupList.sort(function(a, b) {
                if (self.state.autoSortPorts && a.y !== b.y) return a.y - b.y;
                return naturalCompare(a.key, b.key);
            });
            var slot = 0;
            P.slotOf = {};
            P.items = [];
            groupList.forEach(function(g) {
                if (P.headings && P.headings[g.key]) {
                    P.items.push({ heading: g.key, slot: slot, n: 1 });
                    slot += 1;
                }
                g.rows.forEach(function(r) {
                    r.n = Math.max(1, r.rears.length);
                    r.slot = slot;
                    if (r.front) P.slotOf[r.front.id] = slot + (r.n - 1) / 2;
                    r.rears.forEach(function(rp, i) { P.slotOf[rp.id] = slot + i; });
                    slot += r.n;
                    P.items.push(r);
                });
            });
            P.rows = P.items.filter(function(it) { return !it.heading; });
        });

        // Port-to-node lookup
        var portToNode = {};
        nodeData.forEach(function(nd) {
            nd.ports.forEach(function(p) { portToNode[p.id] = nd; });
        });

        // Compute port Y positions (relative to card top)
        function portRelY(nd, portIdx) {
            var startY = nd._appInfoH ? HEADER_H + nd._appInfoH : HEADER_H;
            return startY + portIdx * (PORT_H + PORT_GAP) + PORT_H / 2;
        }

        // Port position: cable attaches at port container edge (flush with card)
        function getPortPos(portId, otherNodeId) {
            var nd = portToNode[portId];
            if (!nd) return null;
            if (nd._panel) {
                // Fixed side: front ports on the front column's edge, rear ports on the other.
                var slotIdx = nd._panel.slotOf[portId];
                if (slotIdx === undefined) return null;
                var pSide = isFrontId(portId) === nd._panel.frontRight ? 'right' : 'left';
                return {
                    x: pSide === 'right' ? nd.x + cardW(nd) : nd.x,
                    y: nd.y + HEADER_H + slotIdx * (PORT_H + PORT_GAP) + PORT_H / 2,
                    side: pSide,
                };
            }
            var idx = -1;
            for (var i = 0; i < nd.ports.length; i++) {
                if (nd.ports[i].id === portId) { idx = i; break; }
            }
            if (idx < 0) return null;

            var other = otherNodeId ? nodeById[otherNodeId] : null;
            var side = 'right';
            if (other && other.x < nd.x) side = 'left';
            // Stacked under/over a patch panel whose port has a fixed side: leave on that same
            // side, so the cable runs down one rail instead of crossing either card.
            if (other && other._panel && Math.abs(other.x - nd.x) < CARD_W * 1.2) {
                var peer = portPeer[portId];
                if (peer && other._panel.slotOf[peer] !== undefined) {
                    side = isFrontId(peer) === other._panel.frontRight ? 'right' : 'left';
                }
            }

            return {
                x: side === 'right' ? nd.x + cardW(nd) : nd.x,
                y: nd.y + portRelY(nd, idx),
                side: side,
            };
        }

        // Detect parallel cables (multiple edges between same device pair)
        // Assign each an offset index so they fan out instead of overlapping
        var pairCount = {};  // "devA-devB" -> count
        var pairIndex = {};  // edge.id -> index within its pair
        edgeData.forEach(function(e) {
            var s = typeof e.source === 'object' ? e.source.id : e.source;
            var t = typeof e.target === 'object' ? e.target.id : e.target;
            var key = s < t ? s + '|' + t : t + '|' + s;
            if (!pairCount[key]) pairCount[key] = 0;
            pairIndex[e.id] = pairCount[key];
            pairCount[key]++;
        });
        // Store total count per edge
        edgeData.forEach(function(e) {
            var s = typeof e.source === 'object' ? e.source.id : e.source;
            var t = typeof e.target === 'object' ? e.target.id : e.target;
            var key = s < t ? s + '|' + t : t + '|' + s;
            e._pairIdx = pairIndex[e.id];
            e._pairTotal = pairCount[key];
        });

        // Pre-compute channel-based ortho routes
        var CHANNEL_SPACING = 10; // px between cables in a channel

        function precomputeOrthoChannels() {
            // For each edge, compute its channel X position
            // Group edges by column pair, then spread within channel
            var channels = {};

            edgeData.forEach(function(e) {
                var sp = getPortPos(e.source_port, typeof e.target === 'object' ? e.target.id : e.target);
                var tp = getPortPos(e.target_port, typeof e.source === 'object' ? e.source.id : e.source);
                if (!sp || !tp) return;

                var dxAbs = Math.abs(sp.x - tp.x);
                if (dxAbs < CARD_W * 1.2) return; // same-column, handled by side rail

                // Channel key: rounded source and target X positions
                var leftX = Math.min(sp.x, tp.x);
                var rightX = Math.max(sp.x, tp.x);
                var key = Math.round(leftX / 100) + '|' + Math.round(rightX / 100);
                var channelX = (leftX + rightX) / 2;

                if (!channels[key]) channels[key] = { x: channelX, edges: [] };
                channels[key].edges.push({
                    edge: e,
                    avgY: (sp.y + tp.y) / 2,
                });
            });

            // Sort and assign offsets (stored as relative offset, not absolute X)
            Object.keys(channels).forEach(function(key) {
                var ch = channels[key];
                ch.edges.sort(function(a, b) { return a.avgY - b.avgY; });
                var total = ch.edges.length;
                ch.edges.forEach(function(item, idx) {
                    item.edge._channelOffset = (idx - (total - 1) / 2) * CHANNEL_SPACING;
                });
            });
        }

        // Edge position for portless nodes (apps) — attaches at card edge midpoint
        function getNodeEdgePos(nd, otherNd) {
            if (!nd) return null;
            var side = 'right';
            if (otherNd && otherNd.x < nd.x) side = 'left';
            return {
                x: side === 'right' ? nd.x + cardW(nd) : nd.x,
                y: nd.y + (nd._cardH || 60) / 2,
                side: side,
            };
        }

        // Cable path generator
        function cablePath(d) {
            var srcNode = typeof d.source === 'object' ? d.source : nodeById[d.source];
            var tgtNode = typeof d.target === 'object' ? d.target : nodeById[d.target];
            var sp = getPortPos(d.source_port, typeof d.target === 'object' ? d.target.id : d.target);
            var tp = getPortPos(d.target_port, typeof d.source === 'object' ? d.source.id : d.source);
            // Fallback for portless nodes (apps): use card edge midpoint
            if (!sp) sp = getNodeEdgePos(srcNode, tgtNode);
            if (!tp) tp = getNodeEdgePos(tgtNode, srcNode);
            if (!sp || !tp) {
                if (!srcNode || !tgtNode) return '';
                return 'M' + (srcNode.x + cardW(srcNode)/2) + ',' + (srcNode.y + (srcNode._cardH||40)/2)
                    + ' L' + (tgtNode.x + cardW(tgtNode)/2) + ',' + (tgtNode.y + (tgtNode._cardH||40)/2);
            }

            // Check if devices are in the same column (vertical/HA link)
            var dxAbs = Math.abs(sp.x - tp.x);
            var isSameColumn = dxAbs < CARD_W * 1.2;

            // Parallel cable offset
            var fanOffset = 0;
            if (d._pairTotal > 1) {
                fanOffset = (d._pairIdx - (d._pairTotal - 1) / 2) * 6;
            }

            if (isSameColumn) {
                // Same-column (HA): side rail — on the left when the ports leave on the left
                var railX = (sp.side === 'left' && tp.side === 'left')
                    ? Math.min(sp.x, tp.x) - 20 - d._pairIdx * 14
                    : Math.max(sp.x, tp.x) + 20 + d._pairIdx * 14;
                return 'M' + sp.x + ',' + sp.y
                    + ' L' + railX + ',' + sp.y
                    + ' L' + railX + ',' + tp.y
                    + ' L' + tp.x + ',' + tp.y;
            }

            if (self.state.cableStyle === 'ortho') {
                // Channel-based routing: 3-segment path
                // Compute channel X dynamically so it updates on drag
                var chX = (sp.x + tp.x) / 2;
                // Apply pre-computed offset for parallel cables in same channel
                if (d._channelOffset !== undefined) {
                    chX += d._channelOffset;
                }
                return 'M' + sp.x + ',' + sp.y
                    + ' L' + chX + ',' + sp.y
                    + ' L' + chX + ',' + tp.y
                    + ' L' + tp.x + ',' + tp.y;
            }

            // Default: bezier curve
            var cp = Math.max(dxAbs * 0.45, 60);
            var sDir = sp.side === 'right' ? 1 : -1;
            var tDir = tp.side === 'right' ? 1 : -1;

            return 'M' + sp.x + ',' + sp.y
                + ' C' + (sp.x + cp * sDir) + ',' + (sp.y + fanOffset)
                + ' ' + (tp.x + cp * tDir) + ',' + (tp.y + fanOffset)
                + ' ' + tp.x + ',' + tp.y;
        }

        // Run channel pre-computation for ortho mode
        if (self.state.cableStyle === 'ortho') {
            precomputeOrthoChannels();
        }

        // Cable color helper — physical cable color or speed color
        // Lightens very dark cables so they're visible on dark backgrounds
        function lightenIfDark(hex) {
            if (!hex) return '#6c757d';
            var c = hex.replace('#', '');
            if (c.length === 3) c = c[0]+c[0]+c[1]+c[1]+c[2]+c[2];
            var r = parseInt(c.substring(0,2), 16);
            var g = parseInt(c.substring(2,4), 16);
            var b = parseInt(c.substring(4,6), 16);
            // If cable is too dark (brightness < 40), lighten it
            if ((r + g + b) / 3 < 40) {
                return '#' + Math.min(r+80,255).toString(16).padStart(2,'0')
                    + Math.min(g+80,255).toString(16).padStart(2,'0')
                    + Math.min(b+80,255).toString(16).padStart(2,'0');
            }
            return hex;
        }

        function getCableColor(d) {
            if (self.state.cableColorMode === 'speed') {
                var spd = d.source_port_speed || d.target_port_speed;
                return spd ? App.speedColor(spd) : '#6c757d';
            }
            return lightenIfDark(d.color) || '#6c757d';
        }

        // Base width of a line: an aggregated trunk is thicker the more fibres it carries
        function edgeWidth(d) {
            if (d.edge_type === 'deployed_on') return 1;
            if (d._count > 1) return 1.5 + Math.min(4, Math.log2(d._count));
            return 1.5;
        }

        // === Draw cables ===
        this.edgeElements = this.g.select('.edge-layer')
            .selectAll('path').data(edgeData).enter().append('path')
            .attr('class', function(d) {
                var c = 'topo-edge';
                if (d.status_value === 'planned') c += ' planned';
                if (d._virtual) c += ' virtual';
                return c;
            })
            .attr('stroke', function(d) { return getCableColor(d); })
            .attr('stroke-width', edgeWidth)
            .attr('stroke-opacity', function(d) {
                if (d.edge_type === 'deployed_on') return 0.2;
                return 0.7;
            })
            .attr('stroke-dasharray', function(d) {
                if (d.dependency_type === 'soft') return '12,4,3,4';  // long-dash-dot
                if (d.edge_type === 'deployed_on') return '2,5';
                return null;  // hard deps = solid
            })
            .attr('stroke-linecap', 'round')
            .attr('fill', 'none')
            .attr('d', cablePath)
            .attr('marker-end', function(d) {
                if (!d.directed) return null;
                var color = getCableColor(d).replace('#', '');
                self._ensureArrow(color);
                return 'url(#arrow-' + color + ')';
            })
            .on('click', function(ev, d) { ev.stopPropagation(); if (d.url) window.open(d.url, '_blank'); });

        this.edgeElements.append('title').text(function(d) {
            if (d._members) {
                var head = [d.source_port_name, '\u2192', d.target_port_name].join(' ');
                var lines = d._members.slice(0, 48).map(function(m) {
                    return (m.cable_label || ('#' + m.cable_id)) + '  ' + (m.source_port_name || '') + ' \u2192 ' + (m.target_port_name || '');
                });
                if (d._members.length > 48) lines.push('\u2026 +' + (d._members.length - 48));
                return (d.cable_label || '') + '\n' + head + '\n\n' + lines.join('\n');
            }
            if (d.edge_type === 'deployed_on') return 'Deployed on: ' + (d.label || '');
            if (d.edge_type === 'dependency') {
                var parts = [d.source_port_name, '\u2192', d.target_port_name];
                if (d.dependency_type) parts.push('(' + d.dependency_type + ')');
                if (d.cable_type) parts.push(d.cable_type);
                return parts.filter(Boolean).join(' ');
            }
            return [d.source_port_name, '\u2192', d.target_port_name, d.cable_type].filter(Boolean).join(' ');
        });

        // Give each cable path an ID for textPath reference
        this.edgeElements.attr('id', function(d) { return 'cable-path-' + d.cable_id; });

        // Connector dots container
        var connectorDots = this.g.select('.edge-layer');

        // Create label paths — always left-to-right, horizontal text
        function createLabelPath(d) {
            var sp = getPortPos(d.source_port, typeof d.target === 'object' ? d.target.id : d.target);
            var tp = getPortPos(d.target_port, typeof d.source === 'object' ? d.source.id : d.source);
            if (!sp || !tp) return;

            var pathId = 'cable-label-path-' + d.cable_id;
            var dxAbs = Math.abs(sp.x - tp.x);
            var isSameColumn = dxAbs < CARD_W * 1.2;

            var labelPath;

            if (isSameColumn) {
                // Same-column: horizontal label at the rail midpoint
                var railX = (sp.side === 'left' && tp.side === 'left')
                    ? Math.min(sp.x, tp.x) - 20 - (d._pairIdx || 0) * 14
                    : Math.max(sp.x, tp.x) + 20 + (d._pairIdx || 0) * 14;
                var midY = (sp.y + tp.y) / 2;
                // Short horizontal path at the rail for the text
                labelPath = 'M' + (railX + 4) + ',' + midY + ' L' + (railX + 80) + ',' + midY;
            } else if (self.state.cableStyle === 'ortho') {
                var chX2 = (sp.x + tp.x) / 2 + (d._channelOffset || 0);
                var midY2 = (sp.y + tp.y) / 2;
                labelPath = 'M' + (chX2 - 40) + ',' + midY2 + ' L' + (chX2 + 40) + ',' + midY2;
            } else {
                // Bezier: left-to-right path
                var lp, rp;
                if (sp.x <= tp.x) { lp = sp; rp = tp; }
                else { lp = tp; rp = sp; }
                var dx = Math.abs(rp.x - lp.x);
                var cp = Math.max(dx * 0.45, 60);
                var fanOff = 0;
                if (d._pairTotal > 1) {
                    fanOff = (d._pairIdx - (d._pairTotal - 1) / 2) * 6;
                }
                var lDir = lp === sp ? (sp.side === 'right' ? 1 : -1) : (tp.side === 'right' ? 1 : -1);
                var rDir = rp === sp ? (sp.side === 'right' ? 1 : -1) : (tp.side === 'right' ? 1 : -1);
                labelPath = 'M' + lp.x + ',' + lp.y
                    + ' C' + (lp.x + cp * lDir) + ',' + (lp.y + fanOff)
                    + ' ' + (rp.x + cp * rDir) + ',' + (rp.y + fanOff)
                    + ' ' + rp.x + ',' + rp.y;
            }

            connectorDots.append('path')
                .attr('id', pathId)
                .attr('d', labelPath)
                .attr('fill', 'none')
                .attr('stroke', 'none');
        }

        edgeData.forEach(createLabelPath);

        // Cable labels — "#ID Type" following the label path
        var cableLabels = this.g.select('.edge-layer')
            .selectAll('text.cable-label').data(edgeData).enter().append('text')
            .attr('class', 'cable-label')
            .attr('dy', -5);

        cableLabels.each(function(d) {
            var tp = d3.select(this).append('textPath')
                .attr('href', '#cable-label-path-' + d.cable_id)
                .attr('startOffset', '50%')
                .attr('text-anchor', 'middle');
            if (d._members) {
                tp.append('tspan').attr('class', 'cable-label-id').text(d.cable_label || '');
                return;
            }
            tp.append('tspan').attr('class', 'cable-label-id').text('#' + d.cable_id);
            if (d.cable_type) {
                tp.append('tspan').attr('dx', 5).text(d.cable_type);
            }
        });
        edgeData.forEach(function(d) {
            if (d.edge_type === 'deployed_on') return; // no dots on deployed-on lines
            var sp = getPortPos(d.source_port, typeof d.target === 'object' ? d.target.id : d.target);
            var tp = getPortPos(d.target_port, typeof d.source === 'object' ? d.source.id : d.source);
            var dColor = getCableColor(d);
            if (sp) connectorDots.append('circle').attr('class', 'connector-dot')
                .attr('cx', sp.x).attr('cy', sp.y).attr('r', 2.5)
                .attr('fill', dColor).attr('opacity', 0.8);
            if (tp) connectorDots.append('circle').attr('class', 'connector-dot')
                .attr('cx', tp.x).attr('cy', tp.y).attr('r', 2.5)
                .attr('fill', dColor).attr('opacity', 0.8);
        });

        // Cable hover: show label + highlight, dim others
        this.edgeElements.on('mouseenter', function(ev, d) {
            cableLabels.each(function(ld) {
                if (ld.cable_id === d.cable_id) d3.select(this).classed('visible', true);
            });
            d3.select(this).attr('stroke-opacity', 1).attr('stroke-width', edgeWidth(d) + 1);
            self.edgeElements.filter(function(e) { return e !== d; }).attr('stroke-opacity', 0.12);
        }).on('mouseleave', function() {
            cableLabels.classed('visible', false);
            self.edgeElements
                .attr('stroke-opacity', function(d) { return d.edge_type === 'deployed_on' ? 0.2 : 0.7; })
                .attr('stroke-width', edgeWidth);
        });

        // === Draw device cards ===
        var cards = this.g.select('.node-layer')
            .selectAll('g').data(nodeData).enter().append('g')
            .attr('class', 'topo-stencil-node')
            .attr('transform', function(d) { return 'translate(' + d.x + ',' + d.y + ')'; });

        this.nodeElements = cards;

        // Card shadow (subtle)
        cards.append('rect').attr('class', 'stencil-shadow')
            .attr('x', 2).attr('y', 2)
            .attr('width', cardW).attr('height', function(d) { return d._cardH; })
            .attr('rx', 6).attr('ry', 6)
            .attr('fill', 'rgba(0,0,0,0.15)');

        // Card body
        cards.append('rect').attr('class', 'stencil-bg')
            .attr('width', cardW).attr('height', function(d) { return d._cardH; })
            .attr('rx', 6).attr('ry', 6);

        // Role color top stripe (rounded top corners)
        cards.append('clipPath')
            .attr('id', function(d) { return 'clip-' + d.id; })
            .append('rect')
            .attr('width', cardW).attr('height', function(d) { return d._cardH; })
            .attr('rx', 6).attr('ry', 6);

        cards.append('rect').attr('class', 'stencil-stripe')
            .attr('width', cardW).attr('height', 4)
            .attr('clip-path', function(d) { return 'url(#clip-' + d.id + ')'; })
            .attr('fill', function(d) { return d.role_color || '#6c757d'; });

        // Device name — auto-fits to card width
        cards.append('text').attr('class', 'stencil-name')
            .attr('x', function(d) { return cardW(d) / 2; }).attr('y', 18).attr('text-anchor', 'middle')
            .text(function(d) { return d.name || ''; })
            .each(function(d) {
                // After rendering, check if text is wider than card and compress
                var textW = this.getComputedTextLength();
                var maxTextW = cardW(d) - 16;
                if (textW > maxTextW) {
                    d3.select(this)
                        .attr('textLength', maxTextW)
                        .attr('lengthAdjust', 'spacingAndGlyphs');
                }
            });

        // Device type — auto-fits to card width
        cards.append('text').attr('class', 'stencil-type')
            .attr('x', function(d) { return cardW(d) / 2; }).attr('y', 30).attr('text-anchor', 'middle')
            .text(function(d) { return d.device_type || ''; })
            .each(function(d) {
                var textW = this.getComputedTextLength();
                var maxTextW = cardW(d) - 16;
                if (textW > maxTextW) {
                    d3.select(this)
                        .attr('textLength', maxTextW)
                        .attr('lengthAdjust', 'spacingAndGlyphs');
                }
            });

        // Device status dot (top-right corner, shows offline/failed/decommissioning)
        cards.filter(function(d) { return d.node_type !== 'application'; }).each(function(d) {
            var sc = App.statusColor(d.status_value);
            d3.select(this).append('circle')
                .attr('cx', cardW(d) - 10).attr('cy', 10)
                .attr('r', 4).attr('fill', sc)
                .append('title').text(d.status || '');
        });

        // Separator
        cards.append('line')
            .attr('x1', 4).attr('x2', function(d) { return cardW(d) - 4; })
            .attr('y1', HEADER_H - 1).attr('y2', HEADER_H - 1)
            .attr('stroke', 'rgba(255,255,255,0.08)');

        // App cards: clean professional design — no garish colors
        cards.filter(function(d) { return d.node_type === 'application'; }).each(function(d) {
            var g = d3.select(this);

            // Thin criticality stripe at top
            var critColor = d.criticality_color || '#6c757d';
            g.selectAll('rect').filter(function() {
                var h = d3.select(this).attr('height');
                return h == '3' || h == '4';
            }).attr('fill', critColor);

            // Status indicator: ⚠ icon for host-down, dot for normal
            if (d.host_down) {
                g.append('text')
                    .attr('x', CARD_W - 12).attr('y', 22)
                    .attr('text-anchor', 'middle').attr('fill', '#e74c3c')
                    .attr('font-size', '12px').attr('cursor', 'default')
                    .text('\u26A0');
            } else {
                var statusColor = App.statusColor(d.status_value);
                g.append('circle').attr('cx', CARD_W - 12).attr('cy', 18)
                    .attr('r', 3.5).attr('fill', statusColor);
            }

            // Host-down: show reason text below header instead of group·env
            if (d.host_down && d.host_down_reasons) {
                var reasons = d.host_down_reasons;
                var reasonText = reasons.length === 1
                    ? reasons[0] + ' is down'
                    : reasons.length + ' hosts down';
                g.append('text')
                    .attr('x', CARD_W / 2).attr('y', HEADER_H + 12)
                    .attr('text-anchor', 'middle').attr('fill', '#e74c3c')
                    .attr('font-size', '7.5px').attr('font-weight', '600')
                    .text(reasonText.length > 28 ? reasonText.substring(0, 26) + '..' : reasonText);
            } else {
                // Info line: group · environment
                var infoText = d.group || '';
                if (d.environment) infoText += (infoText ? ' · ' : '') + d.environment;
                if (infoText) {
                    g.append('text')
                        .attr('x', CARD_W / 2).attr('y', HEADER_H + 12)
                        .attr('text-anchor', 'middle').attr('fill', '#585e70')
                        .attr('font-size', '8px')
                        .text(infoText);
                }
            }
        });

        // Draw ports / service slots
        cards.each(function(d) {
            if (!d.ports || d.ports.length === 0) return;
            var g = d3.select(this);
            if (d._panel) { drawPanel(g, d); return; }
            var portStartY = d._appInfoH ? HEADER_H + d._appInfoH : HEADER_H;
            var isApp = d.node_type === 'application';

            d.ports.forEach(function(p, i) {
                var py = portStartY + i * (PORT_H + PORT_GAP);
                var color = p.speed ? App.speedColor(p.speed) : '#556';
                if (p.port_class === 'front-port') color = '#ff9800';
                if (p.port_class === 'rear-port') color = '#795548';
                if (p.port_class === 'dep-outgoing') color = '#4a5568';
                if (p.port_class === 'dep-incoming') color = '#4a5568';

                var pg = g.append('g').attr('class', 'port-container');

                // Section header rows (DEPENDS ON / NEEDED BY)
                if (p.port_class === 'section-header') {
                    pg.append('line')
                        .attr('x1', 6).attr('x2', CARD_W - 6)
                        .attr('y1', py + 2).attr('y2', py + 2)
                        .attr('stroke', 'rgba(255,255,255,0.06)');
                    pg.append('text')
                        .attr('x', 8).attr('y', py + PORT_H / 2 + 3)
                        .attr('fill', '#505868').attr('font-size', '8px')
                        .attr('font-weight', '600').attr('letter-spacing', '0.6px')
                        .text(p.name);
                    return; // skip port rendering for headers
                }

                // Port row background (alternating subtle shade)
                pg.append('rect')
                    .attr('x', 0).attr('y', py)
                    .attr('width', CARD_W).attr('height', PORT_H)
                    .attr('fill', i % 2 === 0 ? 'rgba(255,255,255,0.025)' : 'rgba(0,0,0,0.02)');

                // Color accent bar
                pg.append('rect')
                    .attr('x', 0).attr('y', py + 2)
                    .attr('width', 3).attr('height', PORT_H - 4)
                    .attr('rx', 1)
                    .attr('fill', color);

                // Port name (left side)
                pg.append('text').attr('class', 'port-name')
                    .attr('x', 10)
                    .attr('y', py + PORT_H / 2 + 4)
                    .text(function() {
                        var n = p.name;
                        return n.length > 16 ? n.substring(0, 14) + '..' : n;
                    });

                // Speed/type text (right side, no pill — cleaner)
                var badge = '';
                if (p.speed) badge = App.formatSpeed(p.speed);
                else if (p.port_class === 'front-port') badge = 'FP';
                else if (p.port_class === 'rear-port') badge = 'RP';

                if (badge) {
                    pg.append('text').attr('class', 'port-speed')
                        .attr('x', CARD_W - 8)
                        .attr('y', py + PORT_H / 2 + 4)
                        .attr('text-anchor', 'end')
                        .attr('fill', color)
                        .text(badge);
                }
            });
        });

        // Oriented patch panel: front column | rear column, internal links drawn between them.
        function drawPanel(g, d) {
            var P = d._panel;
            var W = cardW(d);
            var step = PORT_H + PORT_GAP;
            var colW = (W - PANEL_GAP) / 2;
            var frontX = P.frontRight ? W - colW : 0;
            var rearX = P.frontRight ? 0 : W - colW;
            var maxChars = Math.floor((colW - 16) / 6.2);

            // Column captions in the header, on the side of each column
            g.append('text').attr('class', 'port-speed')
                .attr('x', P.frontRight ? W - 8 : 8).attr('y', HEADER_H - 4)
                .attr('text-anchor', P.frontRight ? 'end' : 'start')
                .attr('fill', '#ff9800').attr('font-size', '8px').text('FRONT');
            g.append('text').attr('class', 'port-speed')
                .attr('x', P.frontRight ? 8 : W - 8).attr('y', HEADER_H - 4)
                .attr('text-anchor', P.frontRight ? 'start' : 'end')
                .attr('fill', '#795548').attr('font-size', '8px').text('REAR');

            function toggleCassette(key) {
                if (expanded.has(key)) expanded.delete(key); else expanded.add(key);
                self._growFrom = { id: d.id, h: d._cardH };
                self.events.emit('layout:changed');
                var pos = {};
                nodeData.forEach(function(nd) { pos[nd.id] = { x: nd.x, y: nd.y }; });
                self.state.savedLayout = pos;
                self.render(self.state.nodes, self.state.edges, true);
            }

            function cell(x, y, h, p, color, outerLeft, title) {
                var pg = g.append('g').attr('class', 'port-container');
                if (p._cassette) {
                    pg.style('cursor', 'pointer')
                        .on('click', function(ev) { ev.stopPropagation(); toggleCassette(d.id + '|' + p._cassette); });
                    title = 'Click to unfold cassette ' + p._cassette + ' \u2014';
                }
                pg.append('rect').attr('x', x).attr('y', y).attr('width', colW).attr('height', h)
                    .attr('rx', 2).attr('fill', 'rgba(255,255,255,0.04)')
                    .attr('stroke', 'rgba(127,127,127,0.25)').attr('stroke-width', 0.5);
                pg.append('rect').attr('x', outerLeft ? x : x + colW - 3).attr('y', y + 2)
                    .attr('width', 3).attr('height', h - 4).attr('rx', 1).attr('fill', color);
                var label = p._cassette ? '\u25b8 ' + p.name : p.name;
                var name = label.length > maxChars ? label.substring(0, maxChars - 2) + '..' : label;
                pg.append('text').attr('class', 'port-name')
                    .attr('x', outerLeft ? x + 10 : x + colW - 10)
                    .attr('y', y + h / 2 + 4)
                    .attr('text-anchor', outerLeft ? 'start' : 'end')
                    .text(name);
                pg.append('title').text(title + ' ' + p.name);
            }

            (P.items || []).filter(function(it) { return it.heading; }).forEach(function(it) {
                var y0 = HEADER_H + it.slot * step;
                var hg = g.append('g').attr('class', 'port-container').style('cursor', 'pointer')
                    .on('click', function(ev) { ev.stopPropagation(); toggleCassette(d.id + '|' + it.heading); });
                hg.append('rect').attr('x', 0).attr('y', y0).attr('width', W).attr('height', PORT_H)
                    .attr('fill', 'rgba(127,127,127,0.12)');
                hg.append('text').attr('class', 'port-name').attr('x', W / 2).attr('y', y0 + PORT_H / 2 + 4)
                    .attr('text-anchor', 'middle').text('\u25be ' + it.heading);
                hg.append('title').text('Click to fold cassette ' + it.heading);
            });

            P.rows.forEach(function(r, ri) {
                var y0 = HEADER_H + r.slot * step;
                var h = r.n * step - PORT_GAP;
                g.append('rect').attr('x', 0).attr('y', y0).attr('width', W).attr('height', h)
                    .attr('fill', ri % 2 === 0 ? 'rgba(255,255,255,0.025)' : 'rgba(0,0,0,0.02)');
                if (r.front) cell(frontX, y0, h, r.front, '#ff9800', !P.frontRight, 'Front');
                r.rears.forEach(function(rp, i) {
                    cell(rearX, y0 + i * step, PORT_H, rp, '#795548', P.frontRight, 'Rear');
                });
                // Internal front→rear mapping: the "Y" of a duplex cassette
                if (r.front) {
                    var fEdge = P.frontRight ? frontX : frontX + colW;
                    var rEdge = P.frontRight ? rearX + colW : rearX;
                    r.rears.forEach(function(rp, i) {
                        g.append('path').attr('class', 'panel-mapping')
                            .attr('d', 'M' + fEdge + ',' + (y0 + h / 2) + ' L' + rEdge + ',' + (y0 + i * step + PORT_H / 2))
                            .attr('stroke', '#8a8f98').attr('stroke-width', 1).attr('fill', 'none')
                            .attr('stroke-opacity', 0.7);
                    });
                }
            });
        }

        // Click
        cards.on('click', function(ev, d) {
            ev.stopPropagation();
            var sel = self._multiSel();
            if (ev.ctrlKey || ev.metaKey) {
                // Ctrl/Cmd+click: add to / remove from the multi-selection
                if (sel.has(d.id)) sel.delete(d.id); else sel.add(d.id);
                self._applyMultiSelection();
                return;
            }
            if (!sel.has(d.id) && sel.size) { sel.clear(); self._applyMultiSelection(); }
            self._deselectAll();
            d3.select(this).classed('selected', true);
            self.state.selectedNode = d; self.events.emit('node:select', d);
        });
        self._stencilCards = cards;
        self._applyMultiSelection();
        if (self._raiseId) {
            cards.filter(function(n) { return n.id === self._raiseId; }).raise();
        }
        self._drawGrid(nodeData);

        // Right-click context menu
        cards.on('contextmenu', function(ev, d) {
            ev.preventDefault();
            ev.stopPropagation();
            d3.selectAll('.topo-context-menu').remove();

            var menu = d3.select('body').append('div')
                .attr('class', 'topo-context-menu')
                .style('left', ev.pageX + 'px')
                .style('top', ev.pageY + 'px');

            // --- Info header ---
            menu.append('div').attr('class', 'ctx-header')
                .html('<span class="ctx-dot" style="background:' + (d.role_color || '#6c757d') + '"></span> '
                    + '<strong>' + App.escapeHtml(d.name) + '</strong>');

            menu.append('div').attr('class', 'ctx-divider');

            // --- Open in NetBox ---
            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-open-in-new"></i> Open in NetBox')
                .on('click', function() { window.open(d.url, '_blank'); menu.remove(); });

            // --- Copy name ---
            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-content-copy"></i> Copy name')
                .on('click', function() {
                    navigator.clipboard.writeText(d.name || '');
                    menu.remove();
                });

            // --- Copy IP ---
            if (d.primary_ip) {
                menu.append('div').attr('class', 'ctx-item')
                    .html('<i class="mdi mdi-ip-network"></i> Copy IP (' + App.escapeHtml(d.primary_ip) + ')')
                    .on('click', function() {
                        navigator.clipboard.writeText(d.primary_ip);
                        menu.remove();
                    });
            }

            menu.append('div').attr('class', 'ctx-divider');

            // --- View Apps on this device ---
            if (d.device_id) {
                menu.append('div').attr('class', 'ctx-item')
                    .html('<i class="mdi mdi-graph-outline"></i> View Apps on Device')
                    .on('click', function() {
                        window.location.href = '/plugins/map/topology/?mode=apps&device_ids=' + d.device_id + '&highlight_device=' + d.device_id;
                        menu.remove();
                    });
            }

            // --- Isolate (show only this device + neighbors) ---
            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-focus-field"></i> Isolate connections')
                .on('click', function() {
                    var connectedIds = new Set([d.id]);
                    edgeData.forEach(function(e) {
                        var s = typeof e.source === 'object' ? e.source.id : e.source;
                        var t = typeof e.target === 'object' ? e.target.id : e.target;
                        if (s === d.id) connectedIds.add(t);
                        if (t === d.id) connectedIds.add(s);
                    });
                    self.filterNodes(connectedIds);
                    menu.remove();
                });

            // --- Simulate failure (app and device nodes) ---
            if (d.node_type === 'application' || d.node_type === 'device') {
                if (!self._simulationActive) {
                    menu.append('div').attr('class', 'ctx-item ctx-danger')
                        .html('<i class="mdi mdi-alert-circle"></i> Simulate failure')
                        .on('click', function() {
                            self.simulateFailure(d.id);
                            menu.remove();
                        });
                } else {
                    menu.append('div').attr('class', 'ctx-item')
                        .html('<i class="mdi mdi-close-circle-outline"></i> Clear simulation')
                        .on('click', function() {
                            self.clearSimulation();
                            menu.remove();
                        });
                }
            }

            // --- Show all (reset isolation) ---
            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-eye-outline"></i> Show all devices')
                .on('click', function() {
                    self.filterNodes(null);
                    menu.remove();
                });

            // --- Add neighbors (devices connected but not on canvas) ---
            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-plus-network-outline"></i> Add connected devices')
                .on('click', function() {
                    self.events.emit('device:add-neighbors', d);
                    menu.remove();
                });

            menu.append('div').attr('class', 'ctx-divider');

            // --- Center view ---
            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-crosshairs-gps"></i> Center on device')
                .on('click', function() {
                    var cx = d.x + cardW(d) / 2;
                    var cy = d.y + (d._cardH || 60) / 2;
                    var w = self.width, h = self.height;
                    self.svg.transition().duration(400).call(
                        self.zoom.transform,
                        d3.zoomIdentity.translate(w/2 - cx, h/2 - cy).scale(1)
                    );
                    menu.remove();
                });

            // --- Pin/Unpin position ---
            var isPinned = d._pinned;
            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-pin' + (isPinned ? '-off' : '') + '-outline"></i> '
                    + (isPinned ? 'Unpin position' : 'Pin position'))
                .on('click', function() {
                    d._pinned = !d._pinned;
                    // Sync to state.nodes
                    var orig = self.state.nodes.find(function(n) { return n.id === d.id; });
                    if (orig) orig._pinned = d._pinned;
                    // Visual indicator — pin icon + colored border
                    var cardEl = d3.select(cards.nodes()[nodeData.indexOf(d)]);
                    if (d._pinned) {
                        cardEl.select('.stencil-bg')
                            .attr('stroke', '#f39c12')
                            .attr('stroke-width', 2)
                            .attr('stroke-dasharray', '6,3');
                        // Add pin icon
                        cardEl.selectAll('.pin-indicator').remove();
                        cardEl.append('text').attr('class', 'pin-indicator')
                            .attr('x', cardW(d) - 14).attr('y', 16)
                            .attr('font-family', 'Material Design Icons')
                            .attr('font-size', 14).attr('fill', '#f39c12')
                            .text('\uF403');
                    } else {
                        cardEl.select('.stencil-bg')
                            .attr('stroke', null)
                            .attr('stroke-width', null)
                            .attr('stroke-dasharray', null);
                        cardEl.selectAll('.pin-indicator').remove();
                    }
                    menu.remove();
                });

            menu.append('div').attr('class', 'ctx-divider');

            // --- Remove ---
            menu.append('div').attr('class', 'ctx-item ctx-danger')
                .html('<i class="mdi mdi-close-circle-outline"></i> Remove from canvas')
                .on('click', function() { self.events.emit('device:remove', d.id); menu.remove(); });

            // Close on click elsewhere
            setTimeout(function() {
                d3.select('body').on('click.ctx', function() {
                    d3.selectAll('.topo-context-menu').remove();
                    d3.select('body').on('click.ctx', null);
                });
            }, 10);
        });

        // Hover
        cards.on('mouseenter', function(ev, d) {
            self.edgeElements.attr('stroke-opacity', function(e) {
                var s = typeof e.source === 'object' ? e.source.id : e.source;
                var t = typeof e.target === 'object' ? e.target.id : e.target;
                return (s === d.id || t === d.id) ? 1 : 0.06;
            }).attr('stroke-width', function(e) {
                var s = typeof e.source === 'object' ? e.source.id : e.source;
                var t = typeof e.target === 'object' ? e.target.id : e.target;
                return (s === d.id || t === d.id) ? edgeWidth(e) + 1.5 : edgeWidth(e);
            });
        });
        cards.on('mouseleave', function() {
            self.edgeElements.attr('stroke-opacity', null).attr('stroke-width', edgeWidth);
        });

        // Redraw cables, their label paths and connector dots after cards moved
        function redrawEdges() {
            self.edgeElements.attr('d', cablePath);
            edgeData.forEach(function(e) {
                connectorDots.select('#cable-label-path-' + e.cable_id).remove();
                createLabelPath(e);
            });
            connectorDots.selectAll('circle.connector-dot').remove();
            edgeData.forEach(function(e) {
                var sp = getPortPos(e.source_port, typeof e.target === 'object' ? e.target.id : e.target);
                var tp = getPortPos(e.target_port, typeof e.source === 'object' ? e.source.id : e.source);
                var ec = getCableColor(e);
                if (sp) connectorDots.append('circle').attr('class', 'connector-dot')
                    .attr('cx', sp.x).attr('cy', sp.y).attr('r', 3.5).attr('fill', ec);
                if (tp) connectorDots.append('circle').attr('class', 'connector-dot')
                    .attr('cx', tp.x).attr('cy', tp.y).attr('r', 3.5).attr('fill', ec);
            });
        }

        // Move the multi-selection by (dx, dy) — arrow keys. Cards and cables follow at once;
        // ports are re-sorted and panels re-oriented once the keys are released.
        self._nudgeSelection = function(dx, dy) {
            var sel = self._multiSel();
            var moved = nodeData.filter(function(nd) { return sel.has(nd.id); });
            if (!moved.length) return false;
            moved.forEach(function(nd) {
                nd.x += dx; nd.y += dy;
                var orig = self.state.nodes.find(function(n) { return n.id === nd.id; });
                if (orig) { orig.x = nd.x; orig.y = nd.y; }
            });
            cards.filter(function(nd) { return sel.has(nd.id); })
                .attr('transform', function(nd) { return 'translate(' + nd.x + ',' + nd.y + ')'; });
            redrawEdges();
            self.events.emit('layout:changed');
            clearTimeout(self._nudgeTimer);
            self._nudgeTimer = setTimeout(function() {
                var pos = {};
                nodeData.forEach(function(nd) { pos[nd.id] = { x: nd.x, y: nd.y }; });
                self.state.savedLayout = pos;
                self.render(self.state.nodes, self.state.edges, true);
            }, 400);
            return true;
        };

        // Drag — update cables, snap to grid if enabled or shift held
        cards.call(d3.drag()
            .on('start', function(ev, d) {
                // Store raw (unsnapped) position for smooth dragging
                d._rawX = d.x;
                d._rawY = d.y;
                d._dragStartX = d.x;
                d._dragStartY = d.y;
                // Dragging a card of the multi-selection moves the whole selection
                var sel = self._multiSel();
                d._group = sel.has(d.id) && sel.size > 1
                    ? nodeData.filter(function(nd) { return sel.has(nd.id) && nd !== d; })
                    : [];
                d._group.forEach(function(nd) { nd._dragStartX = nd.x; nd._dragStartY = nd.y; });
            })
            .on('drag', function(ev, d) {
                // Accumulate raw movement
                d._rawX += ev.dx;
                d._rawY += ev.dy;

                // Apply snap if enabled
                if (self.state.snapToGrid || ev.sourceEvent.shiftKey) {
                    var gs = self.state.gridSize || 20;
                    d.x = Math.round(d._rawX / gs) * gs;
                    d.y = Math.round(d._rawY / gs) * gs;
                } else {
                    d.x = d._rawX;
                    d.y = d._rawY;
                }

                d3.select(this).attr('transform', 'translate(' + d.x + ',' + d.y + ')');
                var orig = self.state.nodes.find(function(n) { return n.id === d.id; });
                if (orig) { orig.x = d.x; orig.y = d.y; }
                if (d._group && d._group.length) {
                    var ddx = d.x - d._dragStartX, ddy = d.y - d._dragStartY;
                    d._group.forEach(function(nd) { nd.x = nd._dragStartX + ddx; nd.y = nd._dragStartY + ddy; });
                    cards.filter(function(nd) { return d._group.indexOf(nd) >= 0; })
                        .attr('transform', function(nd) { return 'translate(' + nd.x + ',' + nd.y + ')'; });
                }

                // Notify app renderer overlay so deployed-on edges follow
                if (self.state.topologyMode === 'mixed') {
                    self.events.emit('device:drag', { id: d.id, x: d.x, y: d.y });
                }

                redrawEdges();
            })
            .on('end', function(ev, d) {
                // Only re-sort if device actually moved (not just a click)
                var moved = Math.abs(d.x - d._dragStartX) > 2 || Math.abs(d.y - d._dragStartY) > 2;
                (d._group || []).forEach(function(nd) {
                    var o = self.state.nodes.find(function(n) { return n.id === nd.id; });
                    if (o) { o.x = nd.x; o.y = nd.y; }
                });
                if (moved) self.events.emit('layout:changed');
                var hasPanels = nodeData.some(function(nd) { return nd._panel; });
                if (moved && (self.state.autoSortPorts || hasPanels) && self.state.topologyMode !== 'mixed') {
                    // Sync all positions to state.nodes first
                    nodeData.forEach(function(nd) {
                        var orig = self.state.nodes.find(function(n) { return n.id === nd.id; });
                        if (orig) { orig.x = nd.x; orig.y = nd.y; }
                    });
                    // Re-render with positions preserved
                    var pos = {};
                    nodeData.forEach(function(nd) { pos[nd.id] = { x: nd.x, y: nd.y }; });
                    self.state.savedLayout = pos;
                    self.render(self.state.nodes, self.state.edges, true);
                    self.events.emit('data:loaded', { nodes: self.state.nodes, edges: self.state.edges });
                }
            })
        );

        // Sync final positions back to state.nodes so save/toggle works
        nodeData.forEach(function(d) {
            var orig = self.state.nodes.find(function(n) { return n.id === d.id; });
            if (orig) { orig.x = d.x; orig.y = d.y; }
        });

        if (!self._skipFit) {
            setTimeout(function() { self.fitToView(); }, 50);
        }
    };

    /* ================================================================
       APP STENCIL VIEW — Application cards with dependency edges
       ================================================================ */

    var APP_CARD_W = 200;
    var APP_CARD_H = 80;
    var APP_CARD_R = 12;
    var APP_BAR_W = 6;

    // Returns the edge midpoint {x, y, side} for connecting a bezier to a card edge
    function getNodeEdgePos(nd, otherNd) {
        if (!nd) return null;
        var cx = nd.x + APP_CARD_W / 2;
        var cy = nd.y + APP_CARD_H / 2;
        var ox = otherNd ? otherNd.x + APP_CARD_W / 2 : cx + 1;
        var oy = otherNd ? otherNd.y + APP_CARD_H / 2 : cy;
        var dx = ox - cx;
        var dy = oy - cy;
        // Determine which side the edge exits from
        if (Math.abs(dx) * APP_CARD_H > Math.abs(dy) * APP_CARD_W) {
            // Left or right
            if (dx > 0) return { x: nd.x + APP_CARD_W, y: cy, side: 'right' };
            else return { x: nd.x, y: cy, side: 'left' };
        } else {
            // Top or bottom
            if (dy > 0) return { x: cx, y: nd.y + APP_CARD_H, side: 'bottom' };
            else return { x: cx, y: nd.y, side: 'top' };
        }
    }

    Renderer.prototype._renderAppStencil = function(nodes, edges) {
        var self = this;
        this._updateSize();
        this.g.selectAll('.edge-layer > *, .node-layer > *, .overlay-node-layer > *, .highlight-layer > *').remove();
        if (this.simulation) { this.simulation.stop(); this.simulation = null; }
        if (nodes.length === 0) return;

        var nodeData = nodes.map(function(n) {
            return Object.assign({}, n, { _cardW: APP_CARD_W, _cardH: APP_CARD_H });
        });
        var edgeData = edges.map(function(e) { return Object.assign({}, e); });

        var nodeById = {};
        nodeData.forEach(function(n) { nodeById[n.id] = n; });

        // Apply saved positions
        var savedLayout = self.state.savedLayout;
        if (savedLayout && typeof savedLayout === 'object') {
            nodeData.forEach(function(n) {
                var saved = savedLayout[n.id];
                if (saved && saved.x !== undefined) {
                    n.x = saved.x;
                    n.y = saved.y;
                    n.fx = saved.x;
                    n.fy = saved.y;
                }
            });
        }

        // Store for external access
        this._stencilNodeData = nodeData;

        // Dependency edge bezier path
        function depPath(d) {
            var srcNode = typeof d.source === 'object' ? d.source : nodeById[d.source];
            var tgtNode = typeof d.target === 'object' ? d.target : nodeById[d.target];
            if (!srcNode || !tgtNode) return '';
            var sp = getNodeEdgePos(srcNode, tgtNode);
            var tp = getNodeEdgePos(tgtNode, srcNode);
            if (!sp || !tp) return '';
            var dx = Math.abs(sp.x - tp.x);
            var cp = Math.max(dx * 0.4, 60);
            var sDir = sp.side === 'right' ? 1 : (sp.side === 'left' ? -1 : 0);
            var tDir = tp.side === 'right' ? 1 : (tp.side === 'left' ? -1 : 0);
            var sdy = sp.side === 'bottom' ? 1 : (sp.side === 'top' ? -1 : 0);
            var tdy = tp.side === 'bottom' ? 1 : (tp.side === 'top' ? -1 : 0);
            return 'M' + sp.x + ',' + sp.y
                + ' C' + (sp.x + cp * sDir) + ',' + (sp.y + cp * sdy)
                + ' ' + (tp.x + cp * tDir) + ',' + (tp.y + cp * tdy)
                + ' ' + tp.x + ',' + tp.y;
        }

        // Get arrow marker ID from edge color
        function arrowId(color) {
            var hex = (color || '#6c757d').replace('#', '');
            return 'arrow-' + hex;
        }

        // === Draw dependency edges ===
        this.edgeElements = this.g.select('.edge-layer')
            .selectAll('path').data(edgeData).enter().append('path')
            .attr('class', function(d) {
                var c = 'topo-edge topo-dep-edge';
                if (d.dependency_type === 'soft') c += ' soft';
                return c;
            })
            .attr('stroke', function(d) { return d.color || '#6c757d'; })
            .attr('stroke-width', 2)
            .attr('fill', 'none')
            .attr('marker-end', function(d) { return 'url(#' + arrowId(d.color) + ')'; })
            .attr('d', depPath);

        this.edgeElements.append('title').text(function(d) {
            var parts = [d.dependency_type];
            if (d.label) parts.push(d.label);
            return parts.join(' | ');
        });

        // === Draw app cards ===
        var cards = this.g.select('.node-layer')
            .selectAll('g').data(nodeData).enter().append('g')
            .attr('class', 'topo-stencil-node topo-stencil-app')
            .attr('transform', function(d) { return 'translate(' + (d.x || 0) + ',' + (d.y || 0) + ')'; });

        this.nodeElements = cards;

        // Card shadow
        cards.append('rect').attr('class', 'stencil-shadow')
            .attr('x', 2).attr('y', 2)
            .attr('width', APP_CARD_W).attr('height', APP_CARD_H)
            .attr('rx', APP_CARD_R).attr('ry', APP_CARD_R)
            .attr('fill', 'rgba(0,0,0,0.15)');

        // Card body
        cards.append('rect').attr('class', 'stencil-bg')
            .attr('width', APP_CARD_W).attr('height', APP_CARD_H)
            .attr('rx', APP_CARD_R).attr('ry', APP_CARD_R);

        // Left color bar (clipped to rounded corners)
        cards.append('clipPath')
            .attr('id', function(d) { return 'appclip-' + d.id; })
            .append('rect')
            .attr('width', APP_CARD_W).attr('height', APP_CARD_H)
            .attr('rx', APP_CARD_R).attr('ry', APP_CARD_R);

        cards.append('rect').attr('class', 'app-left-bar')
            .attr('width', APP_BAR_W).attr('height', APP_CARD_H)
            .attr('clip-path', function(d) { return 'url(#appclip-' + d.id + ')'; })
            .attr('fill', function(d) { return d.category_color || d.role_color || '#6c757d'; });

        // App name — auto-fits
        var maxTextW = APP_CARD_W - APP_BAR_W - 16;
        cards.append('text').attr('class', 'app-name stencil-name')
            .attr('x', APP_BAR_W + 10).attr('y', 24)
            .text(function(d) { return d.name || ''; })
            .each(function() {
                var textW = this.getComputedTextLength();
                if (textW > maxTextW) {
                    d3.select(this)
                        .attr('textLength', maxTextW)
                        .attr('lengthAdjust', 'spacingAndGlyphs');
                }
            });

        // Environment/type subtitle
        cards.append('text').attr('class', 'app-type stencil-type')
            .attr('x', APP_BAR_W + 10).attr('y', 38)
            .text(function(d) {
                var parts = [];
                if (d.environment) parts.push(d.environment);
                if (d.group) parts.push(d.group);
                return parts.join(' \u2022 ') || '';
            })
            .each(function() {
                var textW = this.getComputedTextLength();
                if (textW > maxTextW) {
                    d3.select(this)
                        .attr('textLength', maxTextW)
                        .attr('lengthAdjust', 'spacingAndGlyphs');
                }
            });

        // Status dot
        cards.append('circle').attr('class', 'app-status')
            .attr('cx', APP_BAR_W + 14).attr('cy', 56)
            .attr('r', 4)
            .attr('fill', function(d) { return App.statusColor(d.status_value); });

        // Status text
        cards.append('text').attr('class', 'app-status')
            .attr('x', APP_BAR_W + 22).attr('y', 59)
            .attr('font-size', '9px').attr('fill', '#a0a8c0')
            .text(function(d) { return d.status || ''; });

        // Criticality badge
        cards.append('text').attr('class', 'app-criticality')
            .attr('x', APP_CARD_W - 10).attr('y', 59)
            .attr('text-anchor', 'end')
            .attr('fill', function(d) { return d.criticality_color || '#6c757d'; })
            .text(function(d) {
                return d.criticality ? d.criticality.toUpperCase() : '';
            });

        // Separator line
        cards.append('line')
            .attr('x1', APP_BAR_W + 4).attr('x2', APP_CARD_W - 4)
            .attr('y1', APP_CARD_H - 18).attr('y2', APP_CARD_H - 18)
            .attr('stroke', 'rgba(255,255,255,0.06)');

        // Owner / deploy count
        cards.append('text')
            .attr('x', APP_BAR_W + 10).attr('y', APP_CARD_H - 5)
            .attr('font-size', '8px').attr('fill', '#6070a0')
            .text(function(d) {
                var parts = [];
                if (d.owner) parts.push(d.owner);
                if (d.deploy_count) parts.push(d.deploy_count + ' hosts');
                return parts.join(' \u2022 ');
            });

        // Click to select
        cards.on('click', function(ev, d) {
            ev.stopPropagation(); self._deselectAll();
            d3.select(this).classed('selected', true);
            self.state.selectedNode = d; self.events.emit('node:select', d);
        });

        // Right-click context menu
        cards.on('contextmenu', function(ev, d) {
            ev.preventDefault();
            ev.stopPropagation();
            d3.selectAll('.topo-context-menu').remove();

            var menu = d3.select('body').append('div')
                .attr('class', 'topo-context-menu')
                .style('left', ev.pageX + 'px')
                .style('top', ev.pageY + 'px');

            menu.append('div').attr('class', 'ctx-header')
                .html('<span class="ctx-dot" style="background:' + (d.category_color || '#6c757d') + '"></span> '
                    + '<strong>' + App.escapeHtml(d.name) + '</strong>');

            menu.append('div').attr('class', 'ctx-divider');

            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-open-in-new"></i> Open in NetBox')
                .on('click', function() { window.open(d.url, '_blank'); menu.remove(); });

            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-content-copy"></i> Copy name')
                .on('click', function() {
                    navigator.clipboard.writeText(d.name || '');
                    menu.remove();
                });

            menu.append('div').attr('class', 'ctx-divider');

            // --- Simulate failure ---
            if (!self._simulationActive) {
                menu.append('div').attr('class', 'ctx-item ctx-danger')
                    .html('<i class="mdi mdi-alert-circle"></i> Simulate failure')
                    .on('click', function() {
                        self.simulateFailure(d.id);
                        menu.remove();
                    });
            } else {
                menu.append('div').attr('class', 'ctx-item')
                    .html('<i class="mdi mdi-close-circle-outline"></i> Clear simulation')
                    .on('click', function() {
                        self.clearSimulation();
                        menu.remove();
                    });
            }

            menu.append('div').attr('class', 'ctx-divider');

            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-crosshairs-gps"></i> Center on app')
                .on('click', function() {
                    var cx = d.x + APP_CARD_W / 2;
                    var cy = d.y + APP_CARD_H / 2;
                    var w = self.width, h = self.height;
                    self.svg.transition().duration(400).call(
                        self.zoom.transform,
                        d3.zoomIdentity.translate(w/2 - cx, h/2 - cy).scale(1)
                    );
                    menu.remove();
                });

            // Pin/Unpin
            var isPinned = d._pinned;
            menu.append('div').attr('class', 'ctx-item')
                .html('<i class="mdi mdi-pin' + (isPinned ? '-off' : '') + '-outline"></i> '
                    + (isPinned ? 'Unpin position' : 'Pin position'))
                .on('click', function() {
                    d._pinned = !d._pinned;
                    if (d._pinned) {
                        d.fx = d.x; d.fy = d.y;
                    } else {
                        d.fx = null; d.fy = null;
                        if (self.simulation) self.simulation.alpha(0.3).restart();
                    }
                    menu.remove();
                });

            setTimeout(function() {
                d3.select('body').on('click.ctx', function() {
                    d3.selectAll('.topo-context-menu').remove();
                    d3.select('body').on('click.ctx', null);
                });
            }, 10);
        });

        // Hover: highlight connected edges
        cards.on('mouseenter', function(ev, d) {
            self.edgeElements.attr('stroke-opacity', function(e) {
                var s = typeof e.source === 'object' ? e.source.id : e.source;
                var t = typeof e.target === 'object' ? e.target.id : e.target;
                return (s === d.id || t === d.id) ? 1 : 0.08;
            }).attr('stroke-width', function(e) {
                var s = typeof e.source === 'object' ? e.source.id : e.source;
                var t = typeof e.target === 'object' ? e.target.id : e.target;
                return (s === d.id || t === d.id) ? 3 : 1.5;
            });
        });
        cards.on('mouseleave', function() {
            self.edgeElements.attr('stroke-opacity', null).attr('stroke-width', 2);
        });

        // Force-directed layout
        this.simulation = d3.forceSimulation(nodeData)
            .force('link', d3.forceLink(edgeData).id(function(d) { return d.id; }).distance(250).strength(0.5))
            .force('charge', d3.forceManyBody().strength(-500).distanceMax(800))
            .force('center', d3.forceCenter(this.width / 2, this.height / 2))
            .force('collision', d3.forceCollide().radius(110))
            .alphaDecay(0.03)
            .on('tick', function() {
                cards.attr('transform', function(d) { return 'translate(' + d.x + ',' + d.y + ')'; });
                self.edgeElements.attr('d', depPath);
            });
        this.simulation.on('end', function() {
            if (!self._skipFit) self.fitToView();
        });

        // Drag with force sim
        cards.call(d3.drag()
            .on('start', function(ev, d) {
                if (!ev.active && self.simulation) self.simulation.alphaTarget(0.1).restart();
                d.fx = d.x; d.fy = d.y;
            })
            .on('drag', function(ev, d) {
                d.fx = ev.x; d.fy = ev.y;
            })
            .on('end', function(ev, d) {
                if (!ev.active && self.simulation) self.simulation.alphaTarget(0);
                if (!d._pinned) { d.fx = null; d.fy = null; }
            })
        );

        // Sync positions to state
        nodeData.forEach(function(d) {
            var orig = self.state.nodes.find(function(n) { return n.id === d.id; });
            if (orig) { orig.x = d.x; orig.y = d.y; }
        });

        if (!self._skipFit) {
            setTimeout(function() { self.fitToView(); }, 50);
        }
    };

    /* ================================================================
       NODE VIEW
       ================================================================ */

    Renderer.prototype._renderNodes = function(nodes, edges) {
        var self = this;
        this._updateSize();
        this.g.selectAll('.edge-layer > *, .node-layer > *, .overlay-node-layer > *, .highlight-layer > *').remove();
        if (this.simulation) this.simulation.stop();
        if (nodes.length === 0) return;

        var nd = nodes.map(function(n) { return Object.assign({}, n); });
        var ed = edges.map(function(e) { return Object.assign({}, e); });

        this.edgeElements = this.g.select('.edge-layer')
            .selectAll('line').data(ed).enter().append('line')
            .attr('class', 'topo-edge')
            .attr('stroke', function(d) {
                if (self.state.cableColorMode === 'speed') {
                    var spd = d.source_port_speed || d.target_port_speed;
                    return spd ? App.speedColor(spd) : '#6c757d';
                }
                return d.color || '#6c757d';
            })
            .attr('stroke-width', 2)
            .on('click', function(ev, d) { ev.stopPropagation(); if (d.url) window.open(d.url, '_blank'); });

        this.edgeElements.append('title').text(function(d) {
            return [d.cable_label, d.cable_type, d.status].filter(Boolean).join(' \u2022 ');
        });

        var ng = this.g.select('.node-layer')
            .selectAll('g').data(nd).enter().append('g')
            .attr('class', 'topo-node')
            .call(d3.drag()
                .on('start', function(ev, d) { if (!ev.active && self.simulation) self.simulation.alphaTarget(0.1).restart(); d.fx = d.x; d.fy = d.y; })
                .on('drag', function(ev, d) { d.fx = ev.x; d.fy = ev.y; })
                .on('end', function(ev, d) { if (!ev.active && self.simulation) self.simulation.alphaTarget(0); d.fx = null; d.fy = null; })
            );
        this.nodeElements = ng;

        var nr = function(d) { return d.interface_count > 24 ? 24 : 18; };
        ng.append('circle').attr('class', 'node-bg').attr('r', nr).attr('fill', function(d) { return d.role_color || '#6c757d'; });
        ng.append('text').attr('class', 'node-icon').text(function(d) { return App.roleIcon(d.role_slug); });
        ng.append('circle').attr('class', 'status-dot').attr('r', 4)
            .attr('cx', function(d) { return nr(d) - 2; }).attr('cy', function(d) { return -(nr(d) - 2); })
            .attr('fill', function(d) { return d.host_down ? '#e74c3c' : App.statusColor(d.status_value); });
        ng.append('text').attr('class', 'node-label').attr('dy', function(d) { return nr(d) + 14; })
            .text(function(d) { var n = d.name || ''; return n.length > 20 ? n.substring(0, 18) + '\u2026' : n; });
        ng.filter(function(d) { return d.host_down; }).append('title')
            .text(function(d) {
                var r = d.host_down_reasons || [];
                return r.length === 1 ? r[0] + ' is down' : r.join(', ') + ' are down';
            });

        ng.on('click', function(ev, d) {
            ev.stopPropagation(); self._deselectAll();
            d3.select(this).classed('selected', true);
            self.state.selectedNode = d; self.events.emit('node:select', d);
        });
        ng.on('mouseenter', function(ev, d) {
            self.edgeElements.attr('stroke-opacity', function(e) { return (e.source.id === d.id || e.target.id === d.id) ? 0.9 : 0.12; });
        });
        ng.on('mouseleave', function() { self.edgeElements.attr('stroke-opacity', null); });

        this.simulation = d3.forceSimulation(nd)
            .force('link', d3.forceLink(ed).id(function(d) { return d.id; }).distance(140).strength(0.7))
            .force('charge', d3.forceManyBody().strength(-400).distanceMax(500))
            .force('center', d3.forceCenter(this.width / 2, this.height / 2))
            .force('collision', d3.forceCollide().radius(35))
            .alphaDecay(0.03)
            .on('tick', function() {
                self.edgeElements.attr('x1', function(d) { return d.source.x; }).attr('y1', function(d) { return d.source.y; })
                    .attr('x2', function(d) { return d.target.x; }).attr('y2', function(d) { return d.target.y; });
                ng.attr('transform', function(d) { return 'translate(' + d.x + ',' + d.y + ')'; });
            });
        this.simulation.on('end', function() { self.fitToView(); });
    };

    /* ===== Shared ===== */

    Renderer.prototype.fitToView = function() {
        if (!this.nodeElements || this.nodeElements.empty()) return;
        this._updateSize();
        var b = this.g.node().getBBox();
        if (b.width === 0 || b.height === 0) return;
        var pad = 80;
        var s = Math.min((this.width - pad * 2) / b.width, (this.height - pad * 2) / b.height, 2);
        s = Math.max(s, 0.05);
        this.svg.transition().duration(500).call(this.zoom.transform,
            d3.zoomIdentity.translate(this.width / 2 - (b.x + b.width / 2) * s, this.height / 2 - (b.y + b.height / 2) * s).scale(s));
    };

    Renderer.prototype.zoomIn = function() { this.svg.transition().duration(300).call(this.zoom.scaleBy, 1.3); };
    Renderer.prototype.zoomOut = function() { this.svg.transition().duration(300).call(this.zoom.scaleBy, 0.7); };
    Renderer.prototype.resize = function() { this._updateSize(); };
    Renderer.prototype.switchView = function(m) { this.state.viewMode = m; this.render(this.state.nodes, this.state.edges, true); };
    Renderer.prototype.switchLayout = function() { this.render(this.state.nodes, this.state.edges, true); };
    Renderer.prototype.switchCableStyle = function(style) { this.state.cableStyle = style; this.render(this.state.nodes, this.state.edges, true); };

    Renderer.prototype.highlightNode = function(id) {
        this._deselectAll();
        if (this.nodeElements) this.nodeElements.each(function(d) { if (d.id === id) d3.select(this).classed('selected', true); });
    };

    /**
     * Pan + zoom to center a node on screen.  Works for both stencil (cards)
     * and force-directed (circle) views.
     */
    Renderer.prototype.focusNode = function(id) {
        var self = this;
        if (!this.nodeElements) return;

        // Find the node data
        var target = null;
        this.nodeElements.each(function(d) { if (d.id === id) target = d; });
        if (!target) return;

        this._updateSize();
        var w = this.width, h = this.height;

        // Compute node center (stencil cards use x/y as top-left; circles use x/y as center)
        var cx, cy;
        if (target._cardH !== undefined) {
            // Stencil card — x/y is top-left corner
            cx = target.x + CARD_W / 2;
            cy = target.y + (target._cardH || 60) / 2;
        } else {
            // Force-directed — x/y is center
            cx = target.x;
            cy = target.y;
        }

        // Zoom to a comfortable scale (1.0 = 100%), clamped
        var scale = 1.0;
        self.svg.transition().duration(400).call(
            self.zoom.transform,
            d3.zoomIdentity.translate(w / 2 - cx * scale, h / 2 - cy * scale).scale(scale)
        );

        // Highlight + select
        this.highlightNode(id);
        this.state.selectedNode = target;
        this.events.emit('node:select', target);
    };

    Renderer.prototype.filterNodes = function(vis) {
        if (!this.nodeElements) return;
        this.nodeElements.style('opacity', function(d) { return vis === null || vis.has(d.id) ? 1 : 0.08; });
        if (this.edgeElements) this.edgeElements.style('opacity', function(d) {
            var s = typeof d.source === 'object' ? d.source.id : d.source;
            var t = typeof d.target === 'object' ? d.target.id : d.target;
            return vis === null || (vis.has(s) && vis.has(t)) ? null : 0.03;
        });
    };

    Renderer.prototype.applyHiddenNodes = function(hiddenSet) {
        if (!this.nodeElements) return;
        this.nodeElements.style('opacity', function(d) { return hiddenSet.has(d.id) ? 0.08 : 1; })
            .style('pointer-events', function(d) { return hiddenSet.has(d.id) ? 'none' : null; });
        if (this.edgeElements) this.edgeElements.style('opacity', function(d) {
            var s = typeof d.source === 'object' ? d.source.id : d.source;
            var t = typeof d.target === 'object' ? d.target.id : d.target;
            return (hiddenSet.has(s) || hiddenSet.has(t)) ? 0.03 : null;
        });
    };

    Renderer.prototype._deselectAll = function() {
        if (this.nodeElements) this.nodeElements.classed('selected', false);
        this.state.selectedNode = null;
    };

    // === Impact Simulation ===

    Renderer.prototype.simulateFailure = function(nodeId) {
        var self = this;
        if (!this.nodeElements || !this._stencilNodeData) return;

        var edges = this.state.edges || [];

        // Build reverse adjacency for dependency edges: source depends on target
        // So dependents of X are sources of edges where target === X
        var reverseAdj = {};
        this._stencilNodeData.forEach(function(n) { reverseAdj[n.id] = []; });
        edges.forEach(function(e) {
            if (e.edge_type === 'deployed_on') return; // handled separately
            var s = typeof e.source === 'object' ? e.source.id : e.source;
            var t = typeof e.target === 'object' ? e.target.id : e.target;
            if (reverseAdj[t]) reverseAdj[t].push(s);
        });

        // If failing a device node, find all apps deployed on it first
        var srcNode = this._stencilNodeData.find(function(n) { return n.id === nodeId; });
        var seedIds = [nodeId];
        if (srcNode && srcNode.node_type === 'device') {
            edges.forEach(function(e) {
                if (e.edge_type !== 'deployed_on') return;
                var s = typeof e.source === 'object' ? e.source.id : e.source;
                var t = typeof e.target === 'object' ? e.target.id : e.target;
                // deployed_on: source=app, target=device
                if (t === nodeId) seedIds.push(s);
            });
        }

        // BFS from seed nodes following reverse dependency edges
        var visited = new Set(seedIds);
        var queue = [];
        var impacted = new Set();

        // Mark all seeds (except the source device) as impacted
        seedIds.forEach(function(id) {
            queue.push({ id: id, depth: 0 });
            if (id !== nodeId) impacted.add(id);
        });

        while (queue.length > 0) {
            var item = queue.shift();
            if (item.depth >= 50) continue;
            var dependents = reverseAdj[item.id] || [];
            dependents.forEach(function(depId) {
                if (!visited.has(depId)) {
                    visited.add(depId);
                    impacted.add(depId);
                    queue.push({ id: depId, depth: item.depth + 1 });
                }
            });
        }

        // Store simulation state
        this._simulationActive = true;
        this._simulationSourceId = nodeId;
        this._simulationImpacted = impacted;
        this.state.simulationActive = true;

        // Apply visual classes
        this.nodeElements
            .classed('failure-source', function(d) { return d.id === nodeId; })
            .classed('failure-impacted', function(d) { return impacted.has(d.id); })
            .style('opacity', function(d) {
                if (d.id === nodeId || impacted.has(d.id)) return 1;
                return 0.15;
            });

        // Dim unrelated edges
        if (this.edgeElements) {
            this.edgeElements.style('opacity', function(e) {
                var s = typeof e.source === 'object' ? e.source.id : e.source;
                var t = typeof e.target === 'object' ? e.target.id : e.target;
                var affected = new Set([nodeId]);
                impacted.forEach(function(id) { affected.add(id); });
                return (affected.has(s) && affected.has(t)) ? null : 0.08;
            });
        }

        // Show toast
        var srcNode = this._stencilNodeData.find(function(n) { return n.id === nodeId; });
        var srcName = srcNode ? srcNode.name : nodeId;
        self._showSimToast('Failure of ' + srcName + ' would impact ' + impacted.size + ' application' + (impacted.size !== 1 ? 's' : ''));

        // Add floating clear button
        this._addClearSimButton();
    };

    Renderer.prototype.clearSimulation = function() {
        this._simulationActive = false;
        this._simulationSourceId = null;
        this._simulationImpacted = new Set();
        this.state.simulationActive = false;

        if (this.nodeElements) {
            this.nodeElements
                .classed('failure-source', false)
                .classed('failure-impacted', false)
                .style('opacity', null);
        }
        if (this.edgeElements) {
            this.edgeElements.style('opacity', null);
        }

        // Remove clear button
        var btn = document.getElementById('topo-clear-sim');
        if (btn) btn.remove();
    };

    Renderer.prototype._showSimToast = function(msg) {
        var el = document.createElement('div');
        el.className = 'topo-toast';
        el.textContent = msg;
        document.body.appendChild(el);
        setTimeout(function() { el.classList.add('visible'); }, 10);
        setTimeout(function() { el.classList.remove('visible'); setTimeout(function() { el.remove(); }, 300); }, 3000);
    };

    Renderer.prototype._addClearSimButton = function() {
        var self = this;
        // Remove existing
        var existing = document.getElementById('topo-clear-sim');
        if (existing) existing.remove();

        var btn = document.createElement('button');
        btn.id = 'topo-clear-sim';
        btn.className = 'topo-btn topo-btn-danger topo-sim-clear-btn';
        btn.innerHTML = '<i class="mdi mdi-close-circle-outline"></i> Clear simulation';
        btn.addEventListener('click', function() { self.clearSimulation(); });

        var container = document.querySelector('.topology-graph-area');
        if (container) container.appendChild(btn);
    };

    App.Renderer = Renderer;
})(TopologyApp);

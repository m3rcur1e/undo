const cur1e = require("cur1e-shared");

const UNDO = KeyBind.add("undo_undo", KeyCode.z, "undo");
const REDO = KeyBind.add("undo_redo", KeyCode.z, "undo");
const DEPTH_PREF = "undo-depth";
const DEPTH_DEFAULT = 50;

const CONSTRUCT = ConstructBlock.ConstructBuild;

const actions = [];
const redos = [];
let known = null;
let knownUnit = -1;
let originals = {};
let completed = [];
let begun = {};
let rotations = [];
let expectedRotations = {};
let pendingRot = {};
let begunBreak = {};

function depth(){
    return Core.settings.getInt(DEPTH_PREF, DEPTH_DEFAULT);
}

function afterUpdate(fn){
    Core.app.post(() => Core.app.post(fn));
}

const suppressed = [];
let suppressGen = 0;
function suppressFrame(binds){
    binds.forEach(b => {
        if(b.value.key == KeyCode.unset) return;
        if(!suppressed.some(e => e.bind == b)){
            suppressed.push({bind: b, key: b.value.key});
            b.value.key = KeyCode.unset;
        }
    });
    const gen = ++suppressGen;
    afterUpdate(() => {
        if(gen != suppressGen) return;
        suppressed.forEach(e => e.bind.value.key = e.key);
        suppressed.length = 0;
    });
}

function bindsOn(key){
    const out = [];
    KeyBind.all.each(b => { if(b != UNDO && b != REDO && b.value != null && b.value.key == key) out.push(b); });
    return out;
}

function desktop(){
    const inp = Vars.control.input;
    return (inp instanceof DesktopInput) && Vars.state.isGame() ? inp : null;
}

function unit(){
    return Vars.player == null || Vars.player.dead() ? null : Vars.player.unit();
}

function key2(x, y){
    return x + "," + y;
}

function key3(x, y, breaking){
    return x + "," + y + (breaking ? ",b" : ",p");
}

const IntArr = n => java.lang.reflect.Array.newInstance(java.lang.Integer.TYPE, n);
const ObjArr = n => java.lang.reflect.Array.newInstance(java.lang.Object, n);

function freeze(list){
    const n = list == null ? 0 : list.length;
    if(n == 0) return null;
    const f = {n: n, pos: IntArr(n), meta: IntArr(n), obj: ObjArr(n * 2), extra: null};
    for(let i = 0; i < n; i++){
        let e = list[i];
        let v = e.breaking ? e.original : e;
        f.pos[i] = ((e.x | 0) << 16) | (e.y | 0);
        f.meta[i] = v == null ? 64 : ((v.rotation | 0) & 7) | (((e.to | 0) & 7) << 3) | (e.breaking ? 64 + 128 : 0) | (e.rot ? 256 : 0);
        if(v != null){
            f.obj[i * 2] = v.block == null ? null : v.block;
            f.obj[i * 2 + 1] = v.config == null ? null : v.config;
        }
        let x = e.breaking ? null : freeze(e.replaced);
        if(x != null){
            if(f.extra == null) f.extra = {};
            f.extra[i] = x;
        }
    }
    return f;
}

function thaw(f){
    const out = [];
    if(f == null) return out;
    for(let i = 0; i < f.n; i++){
        let p = f.pos[i], m = f.meta[i];
        let e = {x: p >>> 16, y: p & 0xffff, rotation: m & 7, to: (m >> 3) & 7, breaking: (m & 64) != 0, block: null, config: null};
        let v = {block: f.obj[i * 2], rotation: m & 7, config: f.obj[i * 2 + 1]};
        if(e.breaking){
            e.original = (m & 128) != 0 ? v : null;
        }else{
            e.block = v.block;
            e.config = v.config;
            e.rot = (m & 256) != 0;
            e.replaced = thaw(f.extra == null ? null : f.extra[i]);
        }
        out.push(e);
    }
    return out;
}

function snapshot(u){
    const out = [];
    out.ids = new java.util.IdentityHashMap();
    const q = u.plans;
    for(let i = 0; i < q.size; i++){
        let p = q.get(i);
        out.push({plan: p, x: p.x, y: p.y, rotation: p.rotation, block: p.block, config: p.config, breaking: p.breaking});
        out.ids.put(p, true);
    }
    return out;
}

function sameQueue(u){
    const q = u.plans;
    if(q.size != known.length) return false;
    for(let i = 0; i < q.size; i++){
        if(q.get(i) != known[i].plan) return false;
    }
    return true;
}

function blockAt(x, y){
    const t = Vars.world.tile(x, y);
    return t == null ? null : t.block();
}

const BUILDING_ROTATION = java.lang.Class.forName("mindustry.gen.Building").getField("rotation");
function blockRotation(b){
    return BUILDING_ROTATION.getInt(b);
}

function infoOf(build){
    return {block: build.block, rotation: blockRotation(build), config: build.config()};
}

function posInfo(build){
    const i = infoOf(build);
    i.x = build.tileX();
    i.y = build.tileY();
    return i;
}

function replacedBy(x, y, block){
    const out = [];
    const team = Vars.player.team();
    const off = -((block.size - 1) >> 1);
    for(let dx = 0; dx < block.size; dx++){
        for(let dy = 0; dy < block.size; dy++){
            let t = Vars.world.tile(x + off + dx, y + off + dy);
            if(t == null || t.build == null || t.build.team != team) continue;
            let b = t.build;
            if(b instanceof CONSTRUCT){
                if(b.prevBuild != null && b.prevBuild.size > 0){
                    b.prevBuild.each(pb => { if(!out.some(o => o.x == pb.tileX() && o.y == pb.tileY())) out.push(posInfo(pb)); });
                }else if(b.previous != null && b.previous != Blocks.air && !out.some(o => o.x == b.tileX() && o.y == b.tileY())){
                    out.push({block: b.previous, rotation: blockRotation(b), config: null, x: b.tileX(), y: b.tileY()});
                }
            }else if(b.block != block && !out.some(o => o.x == b.tileX() && o.y == b.tileY())){
                out.push(posInfo(b));
            }
        }
    }
    return out;
}

function captureBreakArea(inp){
    originals = {};
    if(inp.selectX == -1) return;
    const r = Placement.normalizeArea(inp.selectX, inp.selectY, World.toTile(Core.input.mouseWorld().x), World.toTile(Core.input.mouseWorld().y), 0, false, 200);
    const team = Vars.player.team();
    for(let x = r.x; x <= r.x2; x++){
        for(let y = r.y; y <= r.y2; y++){
            let t = Vars.world.tile(x, y);
            if(t == null || t.build == null || t.build.team != team) continue;
            if(t.build instanceof CONSTRUCT) continue;
            originals[key2(t.build.tileX(), t.build.tileY())] = infoOf(t.build);
        }
    }
}

function begunFor(key, block){
    const b = begun[key];
    return b != null && b.block == block ? b.replaced : null;
}

function resetPending(){
    originals = {};
    begun = {};
    begunBreak = {};
}

function push(act){
    actions.push(act);
    const max = depth();
    while(actions.length > max) actions.shift();
}

function prime(){
    const u = unit();
    if(u == null || desktop() == null || (known != null && knownUnit == u.id)) return;
    known = snapshot(u);
    knownUnit = u.id;
    completed = [];
    rotations = [];
    resetPending();
}

function check(){
    const u = unit();
    if(u == null || desktop() == null){
        known = null;
        return;
    }
    if(known != null && knownUnit == u.id && completed.length == 0 && rotations.length == 0 && sameQueue(u)){
        resetPending();
        return;
    }
    const now = snapshot(u);
    if(known == null || knownUnit != u.id){
        known = now;
        knownUnit = u.id;
        completed = [];
        rotations = [];
        resetPending();
        return;
    }

    const added = now.filter(n => !known.ids.containsKey(n.plan));
    const done = {};
    completed.forEach(c => done[key3(c.x, c.y, c.breaking)] = true);
    const removed = known.filter(k => !now.ids.containsKey(k.plan)).filter(k =>
        done[key3(k.x, k.y, k.breaking)] !== true &&
        (k.breaking ? (blockAt(k.x, k.y) != null && blockAt(k.x, k.y) != Blocks.air) : blockAt(k.x, k.y) != k.block && placeable(k))
    );

    if(completed.length > 0){
        const seen = {};
        known.forEach(k => seen[key3(k.x, k.y, k.breaking)] = true);
        added.forEach(a => seen[key3(a.x, a.y, a.breaking)] = true);
        completed.forEach(c => {
            if(seen[key3(c.x, c.y, c.breaking)] === true) return;
            const key = key2(c.x, c.y);
            if(c.breaking){
                added.push({plan: null, x: c.x, y: c.y, breaking: true, original: originals[key] || begunBreak[key] || null});
            }else{
                added.push({plan: null, x: c.x, y: c.y, rotation: c.rotation, block: c.block, config: c.config, breaking: false, replaced: begunFor(key, c.block) || []});
            }
        });
        completed = [];
    }

    added.forEach(a => {
        const key = key2(a.x, a.y);
        if(!a.breaking){
            if(a.plan != null && isRotatePlan(a)){
                a.rot = true;
                a.replaced = [];
            }else if(a.replaced == null){
                a.replaced = begunFor(key, a.block) || replacedBy(a.x, a.y, a.block);
            }
            return;
        }
        if(a.original !== undefined) return;
        const t = Vars.world.tile(a.x, a.y);
        const pre = originals[key] || begunBreak[key];
        a.original = pre != null ? pre :
            (t != null && t.build != null && !(t.build instanceof CONSTRUCT) ? infoOf(t.build) : null);
    });

    const rotated = [];
    if(rotations.length > 0){
        const byTile = {};
        rotations.forEach(r => {
            const k = key2(r.x, r.y);
            const e = byTile[k];
            if(e != null) e.to = r.to;
            else rotated.push(byTile[k] = {x: r.x, y: r.y, block: r.block, rotation: r.from, to: r.to});
        });
        rotations = [];
        for(let i = added.length - 1; i >= 0; i--){
            let a = added[i], r = byTile[key2(a.x, a.y)];
            if(!a.breaking && r != null && r.block == a.block) added.splice(i, 1);
        }
        mergeLateRotations(rotated);
    }

    known = now;
    resetPending();

    if(added.length == 0 && removed.length == 0 && rotated.length == 0) return;
    const act = {added: freeze(added), removed: freeze(removed), rotated: freeze(rotated)};
    added.forEach(a => { if(a.rot) pendingRot[key2(a.x, a.y)] = act; });
    push(act);
    redos.length = 0;
}

function placeable(k){
    const t = Vars.world.tile(k.x, k.y);
    if(t != null && t.build instanceof CONSTRUCT && t.build.current == k.block && t.build.tileX() == k.x && t.build.tileY() == k.y) return true;
    return Build.validPlaceIgnoreUnits(k.block, Vars.player.team(), k.x, k.y, k.rotation, true, true);
}

function isRotatePlan(a){
    const t = Vars.world.tile(a.x, a.y);
    const b = t == null ? null : t.build;
    return b != null && b.team == Vars.player.team() && !(b instanceof CONSTRUCT) && b.block == a.block &&
        b.tileX() == a.x && b.tileY() == a.y && a.block.rotate && blockRotation(b) != a.rotation;
}

function mergeLateRotations(rotated){
    const into = [];
    for(let i = rotated.length - 1; i >= 0; i--){
        let r = rotated[i], k = key2(r.x, r.y), act = pendingRot[k];
        if(act == null) continue;
        delete pendingRot[k];
        if(actions.indexOf(act) < 0) continue;
        if(into.indexOf(act) < 0){
            into.push(act);
            act.lateRot = [];
        }
        act.lateRot.push(r);
        rotated.splice(i, 1);
    }
    into.forEach(act => {
        const list = thaw(act.rotated);
        act.lateRot.forEach(r => {
            const e = list.find(o => o.x == r.x && o.y == r.y);
            if(e != null) e.to = r.to;
            else list.push(r);
        });
        delete act.lateRot;
        act.rotated = freeze(list);
    });
}

function obstacles(x, y, block){
    const out = [];
    const team = Vars.player.team();
    const off = -((block.size - 1) >> 1);
    for(let dx = 0; dx < block.size; dx++){
        for(let dy = 0; dy < block.size; dy++){
            let t = Vars.world.tile(x + off + dx, y + off + dy);
            if(t == null || t.build == null || t.build.team != team) continue;
            let b = t.build, center = b.tileX() == x && b.tileY() == y;
            if(out.indexOf(b) >= 0) continue;
            if(b instanceof CONSTRUCT){
                if(b.current == block && center) continue;
            }else if((b.block == block && center) || block.canReplace(b.block)){
                continue;
            }
            out.push(b);
        }
    }
    return out;
}

function hasPlan(u, x, y, breaking){
    const q = u.plans;
    for(let i = 0; i < q.size; i++){
        let p = q.get(i);
        if(p.x == x && p.y == y && p.breaking == breaking) return true;
    }
    return false;
}

function placeBack(u, x, y, rotation, block, config){
    const obs = obstacles(x, y, block);
    if(obs.length == 0){
        u.addBuild(new BuildPlan(x, y, rotation, block, config));
        return;
    }
    const q = u.plans;
    let samePos = false;
    obs.forEach(b => {
        const bx = b.tileX(), by = b.tileY();
        if(bx == x && by == y) samePos = true;
        if(hasPlan(u, bx, by, true)) return;
        if(bx == x && by == y) q.addLast(new BuildPlan(bx, by));
        else u.addBuild(new BuildPlan(bx, by));
    });
    if(!samePos){
        u.addBuild(new BuildPlan(x, y, rotation, block, config));
        return;
    }
    for(let i = q.size - 1; i >= 0; i--){
        let p = q.get(i);
        if(p.x == x && p.y == y && !p.breaking) q.removeIndex(i);
    }
    q.addLast(new BuildPlan(x, y, rotation, block, config));
}

function dropAll(u, keys){
    const q = u.plans, keep = [];
    let dropped = 0;
    for(let i = 0; i < q.size; i++){
        let p = q.get(i);
        if(keys[key3(p.x, p.y, p.breaking)] === true) dropped++;
        else keep.push(p);
    }
    if(dropped == 0) return;
    q.clear();
    keep.forEach(p => q.addLast(p));
}

function undo(){
    const u = unit();
    if(u == null) return;
    check();
    const act = actions.pop();
    if(act == null) return;
    const added = thaw(act.added), removed = thaw(act.removed), rotated = thaw(act.rotated);

    const drop = {};
    added.forEach(a => drop[key3(a.x, a.y, a.breaking)] = true);
    rotated.forEach(r => drop[key3(r.x, r.y, false)] = true);
    dropAll(u, drop);

    const team = Vars.player.team();
    added.forEach(a => {
        if(a.rot) return;
        if(!a.breaking){
            const repl = a.replaced;
            const same = repl.find(o => o.x == a.x && o.y == a.y);
            const t = Vars.world.tile(a.x, a.y);
            const now = t != null && t.build != null && t.build.team == team ? t.build : null;
            if(same != null){
                if(blockAt(a.x, a.y) != same.block) placeBack(u, same.x, same.y, same.rotation, same.block, same.config);
            }else if(now != null){
                u.addBuild(new BuildPlan(now.tileX(), now.tileY()));
            }
            repl.forEach(o => { if(o !== same) placeBack(u, o.x, o.y, o.rotation, o.block, o.config); });
        }else if(a.original != null && blockAt(a.x, a.y) != a.original.block){
            placeBack(u, a.x, a.y, a.original.rotation, a.original.block, a.original.config);
        }
    });
    removed.forEach(r => {
        if(r.breaking){
            if(!hasPlan(u, r.x, r.y, true)) u.addBuild(new BuildPlan(r.x, r.y));
        }else if(blockAt(r.x, r.y) != r.block){
            placeBack(u, r.x, r.y, r.rotation, r.block, r.config);
        }
    });
    rotated.forEach(r => {
        if(blockAt(r.x, r.y) == r.block){
            expectedRotations[key2(r.x, r.y)] = r.rotation;
            u.addBuild(new BuildPlan(r.x, r.y, r.rotation, r.block));
        }
    });

    redos.push(act);

    known = snapshot(u);
    knownUnit = u.id;
}

function redo(){
    const u = unit();
    if(u == null) return;
    check();
    const act = redos.pop();
    if(act == null) return;
    const added = thaw(act.added), removed = thaw(act.removed), rotated = thaw(act.rotated);

    const drop = {};
    added.forEach(a => {
        drop[key3(a.x, a.y, true)] = true;
        drop[key3(a.x, a.y, false)] = true;
        if(!a.breaking) a.replaced.forEach(o => drop[key3(o.x, o.y, false)] = true);
    });
    removed.forEach(r => drop[key3(r.x, r.y, r.breaking)] = true);
    rotated.forEach(r => drop[key3(r.x, r.y, false)] = true);
    dropAll(u, drop);

    const turned = {};
    rotated.forEach(r => turned[key2(r.x, r.y)] = true);
    added.forEach(a => {
        if(a.rot){
            const t = Vars.world.tile(a.x, a.y);
            if(turned[key2(a.x, a.y)] !== true && t != null && t.build != null && t.block() == a.block && blockRotation(t.build) != a.rotation){
                u.addBuild(new BuildPlan(a.x, a.y, a.rotation, a.block, a.config));
                pendingRot[key2(a.x, a.y)] = act;
            }
        }else if(!a.breaking){
            if(blockAt(a.x, a.y) != a.block) placeBack(u, a.x, a.y, a.rotation, a.block, a.config);
        }else{
            const b = blockAt(a.x, a.y);
            if(b != null && b != Blocks.air) u.addBuild(new BuildPlan(a.x, a.y));
        }
    });
    rotated.forEach(r => {
        if(blockAt(r.x, r.y) == r.block){
            expectedRotations[key2(r.x, r.y)] = r.to;
            u.addBuild(new BuildPlan(r.x, r.y, r.to, r.block));
        }
    });

    push(act);

    known = snapshot(u);
    knownUnit = u.id;
}

function guarded(fn){
    try{
        return fn();
    }catch(e){
        Log.err("[undo] " + e);
    }
}

function blocked(){
    return Core.scene.hasKeyboard() || Vars.ui.chatfrag.shown() || Vars.ui.consolefrag.shown() || Core.scene.hasDialog();
}

function ours(unit){
    return unit != null && Vars.player != null && unit == Vars.player.unit();
}

Events.on(BlockBuildEndEvent, e => guarded(() => {
    if(!ours(e.unit)) return;
    if(e.breaking){
        completed.push({x: e.tile.x, y: e.tile.y, breaking: true});
    }else if(e.tile.build != null){
        const b = e.tile.build;
        completed.push({x: b.tileX(), y: b.tileY(), block: b.block, rotation: blockRotation(b), config: e.config, breaking: false});
    }
}));

Events.on(BuildRotateEvent, e => guarded(() => {
    if(!ours(e.unit) || e.build == null) return;
    const b = e.build, key = key2(b.tileX(), b.tileY()), now = blockRotation(b);
    if(expectedRotations[key] === now){
        delete expectedRotations[key];
        return;
    }
    rotations.push({x: b.tileX(), y: b.tileY(), block: b.block, from: e.previous, to: now});
}));

Events.on(BlockBuildBeginEvent, e => guarded(() => {
    if(!ours(e.unit)) return;
    const c = e.tile.build;
    if(!(c instanceof CONSTRUCT)) return;
    const key = key2(c.tileX(), c.tileY());
    if(e.breaking){
        if(c.prevBuild != null && c.prevBuild.size > 0) begunBreak[key] = infoOf(c.prevBuild.first());
    }else{
        begun[key] = {block: c.current, replaced: replacedBy(c.tileX(), c.tileY(), c.current)};
    }
}));

function onKey(key){
    if(key == KeyCode.unset || !Core.input.ctrl() || desktop() == null || blocked()) return;
    const shift = Core.input.shift();
    let fn = null;
    if(key == REDO.value.key && (shift || REDO.value.key != UNDO.value.key)) fn = redo;
    else if(key == UNDO.value.key && !shift) fn = undo;
    if(fn == null) return;
    suppressFrame(bindsOn(key));
    fn();
}

Core.input.addProcessor(extend(InputProcessor, {
    keyDown(key){
        guarded(prime);
        guarded(() => onKey(key));
        return false;
    },
    keyUp(key){
        afterUpdate(() => guarded(check));
        return false;
    },
    touchDown(x, y, pointer, button){
        guarded(prime);
        guarded(() => onKey(button));
        return false;
    },
    touchUp(x, y, pointer, button){
        guarded(() => {
            const inp = desktop();
            if(inp != null && inp.mode == PlaceMode.breaking && button == Binding.breakBlock.value.key) captureBreakArea(inp);
        });
        afterUpdate(() => guarded(check));
        return false;
    }
}));

function keyName(k){
    return k == KeyCode.unset ? "?" : String(k.value);
}

function fromButton(fn){
    if(desktop() == null || blocked()) return;
    fn();
}

Events.on(Packages.mindustry.ui.fragments.HudFragment, req => guarded(() => {
    if(req == null || req.buttons == null) return;
    const b = Core.bundle;
    const redoKey = REDO.value.key != UNDO.value.key ? "Ctrl+" + keyName(REDO.value.key) : "Ctrl+Shift+" + keyName(REDO.value.key);
    req.buttons.push(
        {name: "undo-undo", icon: Icon.undo, order: "b[blueprints]-a[undo]",
            tooltip: b.get("undo.button.undo", "Undo") + " (Ctrl+" + keyName(UNDO.value.key) + ")",
            enabled: () => actions.length > 0, clicked: () => fromButton(undo)},
        {name: "undo-redo", icon: Icon.redo, order: "b[blueprints]-b[redo]",
            tooltip: b.get("undo.button.redo", "Redo") + " (" + redoKey + ")",
            enabled: () => redos.length > 0, clicked: () => fromButton(redo)}
    );
}));

cur1e.settings({mod: "undo", title: "undo.settings", icon: "undo", build: t => {
    t.sliderPref(DEPTH_PREF, DEPTH_DEFAULT, 10, 200, 10, v => "" + v);
}});

Log.info("[undo] loaded");

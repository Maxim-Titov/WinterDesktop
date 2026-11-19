//! Falling snow overlay for Windows.
//! Pure Win32: one layered, click-through, always-on-top window.
//! Snow also settles on the top edge of visible windows and on the taskbar,
//! and falls off again when a window is moved, narrowed, closed or minimized.
//! Hold the left mouse button on a snow pile to roll a snowball out of the fallen snow;
//! drop it on a window / the taskbar / another ball. Three balls stacked = a snowman.
//! A snowman (or ball) shatters back into flakes when its window is moved or resized.
//! When the snow nearly fills the visible top edge of a window / the taskbar, a snowplow truck
//! drives along that edge from right to left and clears it (snowballs and snowmen included).
//! The scene is drawn into a single DIB; only tiny rects around the flakes
//! are cleared and redrawn each frame. Between frames the process sleeps
//! inside GetMessage (0% CPU).
#![windows_subsystem = "windows"]

use std::collections::HashMap;
use std::ffi::c_void;
use std::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use windows::core::{w, PCWSTR};
use windows::Win32::Foundation::{
    BOOL, COLORREF, HINSTANCE, HWND, LPARAM, LRESULT, POINT, RECT, SIZE, WPARAM,
};
use windows::Win32::Graphics::Dwm::{
    DwmGetWindowAttribute, DWMWA_CLOAKED, DWMWA_EXTENDED_FRAME_BOUNDS,
};
use windows::Win32::Graphics::Gdi::{
    CreateCompatibleDC, CreateDIBSection, DeleteDC, DeleteObject, GetMonitorInfoW,
    MonitorFromWindow, SelectObject, AC_SRC_ALPHA, AC_SRC_OVER, BITMAPINFO, BITMAPINFOHEADER,
    BI_RGB, BLENDFUNCTION, DIB_RGB_COLORS, HBITMAP, HDC, HGDIOBJ, MONITORINFO,
    MONITOR_DEFAULTTONEAREST,
};
use windows::Win32::System::LibraryLoader::GetModuleHandleW;
use windows::Win32::System::Threading::{
    GetCurrentProcess, SetPriorityClass, BELOW_NORMAL_PRIORITY_CLASS,
};
use windows::Win32::UI::Shell::{
    SHQueryUserNotificationState, Shell_NotifyIconW, NIF_ICON, NIF_MESSAGE, NIF_TIP, NIM_ADD,
    NIM_DELETE, NOTIFYICONDATAW, QUNS_NOT_PRESENT, QUNS_PRESENTATION_MODE,
    QUNS_RUNNING_D3D_FULL_SCREEN,
};
use windows::Win32::UI::WindowsAndMessaging::*;

// ---- Settings ----
const FLAKE_COUNT: usize = 150; // count of snow
const FPS: u32 = 60;
const MIN_SIZE: f32 = 3.0; // min size, px
const MAX_SIZE: f32 = 9.0; // max size, px
const MIN_SPEED: f32 = 40.0; // speed, px/s
const MAX_SPEED: f32 = 120.0;
const WIND_SWAY: f32 = 25.0; // amplitude of lateral oscillation, px

// ---- Snow piles on windows / taskbar ----
const SCAN_MS: u128 = 50; // how often window positions are re-read
const PILE_MAX: f32 = 14.0; // max snow height on windows, px
const PILE_MAX_TASKBAR: f32 = 8.0; // lower on the taskbar so it doesn't cover content above it
const PILE_RATE: f32 = 0.5; // accumulation speed (bigger = snow piles up faster)
const PILE_SLOPE: f32 = 0.75; // max height difference between neighbouring columns
const PILE_ALPHA: f32 = 235.0; // snow opacity 0..255
const MIN_WIN_W: i32 = 120; // ignore tiny windows
const MIN_WIN_H: i32 = 30;

// ---- Snow falling off moved / resized windows ----
const CHUNK_COLS: i32 = 5; // columns of snow merged into one falling clump
const CHUNK_MAX: usize = 600; // max clumps in the air at once
const CHUNK_KEEP: f32 = 0.6; // share of a clump that sticks if it lands on another window
const GRAVITY: f32 = 1200.0; // px/s^2
const FALL_MAX: f32 = 700.0; // terminal speed, px/s
const CHUNK_IMMUNE: f32 = 0.2; // s before a clump may land (so it doesn't re-land on its own window)

// ---- Snowballs / snowman ----
const BALL_PACK: f32 = 1.5; // ball area per 1 px^2 of loose snow (snow gets packed, so balls grow fast)
const BALL_MAX_R: f32 = 48.0; // max ball radius, px
const BALL_MAX_VOL: f32 = BALL_MAX_R * BALL_MAX_R * 3.141_592_7 / BALL_PACK;
const BALL_GATHER: f32 = 1200.0; // how much snow a held ball scoops per second (px^2/s)
const BALL_SNAP: f32 = 70.0; // max gap between a released ball and its support, px
const BALL_START_VOL: f32 = 24.0; // snow taken from the pile when the ball is created

// ---- Snowplow ----
const PLOW_FULL: f32 = 0.8; // average fill of the visible edge (0..1) that calls the plow
const PLOW_MIN_VISIBLE: i32 = 80; // the visible part of an edge must be at least this long to call a plow
const PLOW_SPEED: f32 = 160.0; // px/s
const PLOW_BLADE: f32 = 40.0; // distance from the truck centre to its blade, px
const PLOW_SPRAY: f32 = 40.0; // snow volume thrown off the blade as one clump

const TIMER_FRAME: usize = 1;
const TIMER_WATCH: usize = 2;
const WM_TRAY: u32 = WM_APP + 1;
const ID_CLOSE: usize = 1001;

// ---- tiny xorshift RNG (no external crates) ----
struct Rng(u64);

impl Rng {
    fn new() -> Self {
        let seed = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0x9E37_79B9_7F4A_7C15);
        Rng(seed | 1)
    }
    fn next_f32(&mut self) -> f32 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        ((x >> 40) as f32) / ((1u64 << 24) as f32) // 0..1
    }
}

struct Flake {
    x: f32,
    y: f32,
    speed: f32,
    phase: f32,
    phase_speed: f32,
    radius: f32,
    opacity: f32,
    rect: (i32, i32, i32, i32), // last drawn rect (x0, y0, x1, y1)
}

/// A window top edge snow can rest on.
struct Surface {
    key: isize,
    left: i32,
    width: i32,
    top: i32,
    max_h: f32,
    segs: Vec<(i32, i32)>, // visible x-spans of the top edge (not covered by windows above)
}

struct Win {
    key: isize,
    l: i32,
    t: i32,
    r: i32,
    b: i32,
    surface: bool,
    taskbar: bool,
}

/// A clump of snow that slid off a window.
struct Chunk {
    x: f32,
    y: f32,
    vx: f32,
    vy: f32,
    vol: f32, // snow volume (px^2), given to whatever it lands on
    radius: f32,
    age: f32,
    rect: (i32, i32, i32, i32), // last drawn rect
}

/// What a ball stands on.
#[derive(Clone, Copy, PartialEq)]
enum Rest {
    /// top edge of a window, geometry remembered: if it changes, the ball shatters
    Surface { key: isize, top: i32, left: i32, width: i32 },
    /// another ball (by id)
    Ball(u32),
}

#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Held,    // follows the cursor (LMB is down)
    Falling, // released, dropping onto its support
    Resting, // stands on its support
}

struct Ball {
    id: u32,
    x: f32,
    y: f32, // centre
    vy: f32,
    vol: f32, // loose snow volume it was made of (given back when it shatters)
    mode: Mode,
    rest: Option<Rest>,
    snowman: bool, // part of a finished snowman
    face: bool,    // the head of a snowman
    rect: (i32, i32, i32, i32),
}

impl Ball {
    fn r(&self) -> f32 {
        (self.vol * BALL_PACK / std::f32::consts::PI).sqrt().min(BALL_MAX_R)
    }
}

/// A snowplow truck driving right -> left along one window edge.
struct Plow {
    key: isize,
    top: i32,
    left: i32,
    width: i32, // geometry of the edge when it started: if it changes, the truck leaves
    x: f32,     // truck centre
    x_end: f32, // it is done when the centre gets here
    carry: f32, // cleared snow not yet thrown off the blade
    t: f32,     // for the flashing beacon
    rect: (i32, i32, i32, i32),
}

struct State {
    hwnd: HWND,
    mem_dc: HDC,
    bitmap: HBITMAP,
    old_obj: HGDIOBJ,
    bits: *mut u32,
    w: i32,
    h: i32,
    flakes: Vec<Flake>,
    rng: Rng,
    last: Instant,
    paused: bool,
    streak: u8, // consecutive checks that disagree with the current state
    surfaces: Vec<Surface>,
    piles: HashMap<isize, Vec<f32>>, // snow height per column, relative to window left
    pile_rects: Vec<(i32, i32, i32, i32)>, // rects drawn last frame (to erase)
    last_scan: Instant,
    force_scan: bool,
    chunks: Vec<Chunk>,
    balls: Vec<Ball>,
    next_ball: u32,
    dead_rects: Vec<(i32, i32, i32, i32)>, // rects of removed balls / plows, to be erased next frame
    plows: Vec<Plow>,
}

/// The low-level mouse hook runs on our own thread (inside GetMessage), so it can reach the state.
static STATE: AtomicPtr<State> = AtomicPtr::new(std::ptr::null_mut());

impl State {
    fn new_flakes(rng: &mut Rng, w: i32, h: i32) -> Vec<Flake> {
        (0..FLAKE_COUNT)
            .map(|_| {
                let size = MIN_SIZE + rng.next_f32() * (MAX_SIZE - MIN_SIZE);
                let depth = (size - MIN_SIZE) / (MAX_SIZE - MIN_SIZE); // 0..1, bigger — faster
                Flake {
                    x: rng.next_f32() * w as f32,
                    y: -rng.next_f32() * h as f32, // start above the screen, staggered, so the snow begins at the top
                    speed: MIN_SPEED + depth * (MAX_SPEED - MIN_SPEED),
                    phase: rng.next_f32() * std::f32::consts::TAU,
                    phase_speed: 0.5 + rng.next_f32(),
                    radius: size / 2.0,
                    opacity: 0.5 + depth * 0.5,
                    rect: (0, 0, 0, 0),
                }
            })
            .collect()
    }

    /// Re-read visible windows (z-order, top to bottom) and work out which parts of
    /// their top edges are actually visible.
    fn rescan(&mut self) {
        let mut list: Vec<HWND> = Vec::with_capacity(128);
        unsafe {
            let _ = EnumWindows(Some(enum_proc), LPARAM(&mut list as *mut Vec<HWND> as isize));
        }
        let (sw, sh) = (self.w, self.h);
        let mut above: Vec<(i32, i32, i32, i32)> = Vec::with_capacity(list.len());
        let mut surfaces: Vec<Surface> = Vec::new();

        for hwnd in list {
            let Some(win) = (unsafe { window_info(hwnd, self.hwnd, sw, sh) }) else {
                continue;
            };
            if win.surface {
                let mut segs = vec![(win.l.max(0), win.r.min(sw))];
                for &(bl, bt, br, bb) in &above {
                    // a window above this one that reaches the top-edge line hides that part
                    if bt <= win.t && bb > win.t {
                        segs = subtract(segs, bl, br);
                        if segs.is_empty() {
                            break;
                        }
                    }
                }
                segs.retain(|&(a, b)| b - a >= 2);
                surfaces.push(Surface {
                    key: win.key,
                    left: win.l,
                    width: win.r - win.l,
                    top: win.t,
                    max_h: if win.taskbar { PILE_MAX_TASKBAR } else { PILE_MAX },
                    segs,
                });
            }
            above.push((win.l, win.t, win.r, win.b));
        }

        // Compare with the previous scan: moved / resized / vanished windows shed their snow
        let old = std::mem::take(&mut self.surfaces);
        let mut new_piles: HashMap<isize, Vec<f32>> = HashMap::with_capacity(surfaces.len());

        for s in &surfaces {
            let n = s.width as usize;
            let o = old.iter().find(|o| o.key == s.key);
            let old_prof = self.piles.remove(&s.key);
            let mut prof = match (o, old_prof) {
                (Some(o), Some(op)) if op.len() == o.width as usize => {
                    let moved = o.top != s.top || (o.width == s.width && o.left != s.left);
                    if moved {
                        // window was moved: all its snow slides off and falls
                        spawn_chunks(&mut self.chunks, &mut self.rng, o, &op);
                        vec![0.0; n]
                    } else if o.width != s.width {
                        // window was resized: snow stays where it lay (screen coordinates),
                        // snow that hung over a removed edge falls
                        let mut keep = vec![0.0f32; n];
                        let mut lost = vec![0.0f32; op.len()];
                        for (j, &v) in op.iter().enumerate() {
                            let i = o.left + j as i32 - s.left;
                            if i >= 0 && i < s.width {
                                keep[i as usize] = v;
                            } else {
                                lost[j] = v;
                            }
                        }
                        spawn_chunks(&mut self.chunks, &mut self.rng, o, &lost);
                        keep
                    } else {
                        op
                    }
                }
                _ => vec![0.0; n],
            };
            // snow lying under another window is gone (and stays gone when it is uncovered again)
            let mut vis = vec![false; n];
            for &(a, b) in &s.segs {
                for x in a.max(s.left)..b.min(s.left + s.width) {
                    vis[(x - s.left) as usize] = true;
                }
            }
            for (v, &ok) in prof.iter_mut().zip(&vis) {
                if !ok {
                    *v = 0.0;
                }
            }
            new_piles.insert(s.key, prof);
        }

        // closed / minimized / maximized / fullscreen windows: their snow falls too
        for o in &old {
            if !surfaces.iter().any(|s| s.key == o.key) {
                if let Some(op) = self.piles.remove(&o.key) {
                    if op.len() == o.width as usize {
                        spawn_chunks(&mut self.chunks, &mut self.rng, o, &op);
                    }
                }
            }
        }

        self.piles = new_piles;
        self.surfaces = surfaces;
        self.check_ball_supports();
        self.check_plows();
    }

    // ---------------------------------------------------------------- snowballs

    fn has_child(&self, id: u32) -> bool {
        self.balls.iter().any(|c| c.rest == Some(Rest::Ball(id)))
    }

    /// Remove ball `i` and let it fall apart into flakes.
    fn drop_ball(&mut self, i: usize) {
        let b = self.balls.swap_remove(i);
        if b.rect.2 > b.rect.0 {
            self.dead_rects.push(b.rect);
        }
        shatter(&mut self.chunks, &mut self.rng, b.x, b.y, b.r(), b.vol);
    }

    /// Balls standing on a window that was moved / resized / closed / covered shatter,
    /// and so does everything stacked on them.
    fn check_ball_supports(&mut self) {
        let mut dead: Vec<u32> = Vec::new();
        for b in &self.balls {
            if let Some(Rest::Surface { key, top, left, width }) = b.rest {
                let ok = self.surfaces.iter().find(|s| s.key == key).map_or(false, |s| {
                    s.top == top
                        && s.left == left
                        && s.width == width
                        && s.segs.iter().any(|&(a, c)| b.x >= a as f32 && b.x < c as f32)
                });
                if !ok {
                    dead.push(b.id);
                }
            }
        }
        if !dead.is_empty() {
            self.kill_balls(dead);
        }
    }

    /// Shatter the given balls and everything stacked on them.
    fn kill_balls(&mut self, mut dead: Vec<u32>) {
        loop {
            let mut added = false;
            for b in &self.balls {
                if let Some(Rest::Ball(id)) = b.rest {
                    if dead.contains(&id) && !dead.contains(&b.id) {
                        dead.push(b.id);
                        added = true;
                    }
                }
            }
            if !added {
                break;
            }
        }
        for i in (0..self.balls.len()).rev() {
            if dead.contains(&self.balls[i].id) {
                self.drop_ball(i);
            }
        }
    }

    // ---------------------------------------------------------------- snowplow

    /// Called after each window scan: plows whose edge changed leave, and a new plow is sent
    /// to every edge whose visible part is nearly full of snow.
    fn check_plows(&mut self) {
        let mut i = 0;
        while i < self.plows.len() {
            let p = &self.plows[i];
            let ok = self
                .surfaces
                .iter()
                .any(|s| s.key == p.key && s.top == p.top && s.left == p.left && s.width == p.width);
            if ok {
                i += 1;
            } else {
                let p = self.plows.remove(i);
                if p.rect.2 > p.rect.0 {
                    self.dead_rects.push(p.rect);
                }
            }
        }

        let mut fresh: Vec<Plow> = Vec::new();
        for s in &self.surfaces {
            if self.plows.iter().any(|p| p.key == s.key) {
                continue;
            }
            let Some(prof) = self.piles.get(&s.key) else { continue };
            let (mut sum, mut cnt) = (0.0f32, 0i32);
            for &(a, b) in &s.segs {
                for x in a..b {
                    let rel = x - s.left;
                    if rel >= 0 && (rel as usize) < prof.len() {
                        sum += prof[rel as usize];
                        cnt += 1;
                    }
                }
            }
            if cnt < PLOW_MIN_VISIBLE || sum < PLOW_FULL * cnt as f32 * s.max_h {
                continue; // too short, or not full enough: no plow needed here
            }
            fresh.push(Plow {
                key: s.key,
                top: s.top,
                left: s.left,
                width: s.width,
                x: (s.left + s.width).min(self.w) as f32 + 45.0,
                x_end: s.left.max(0) as f32 - 45.0,
                carry: 0.0,
                t: 0.0,
                rect: (0, 0, 0, 0),
            });
        }
        self.plows.extend(fresh);
    }

    /// Drive the plows: the blade clears the columns it passes (throwing the snow off),
    /// and shatters every ball / snowman it reaches.
    fn update_plows(&mut self, dt: f32) {
        let mut i = 0;
        while i < self.plows.len() {
            let (key, left, width, top, prev, now, x, x_end) = {
                let p = &mut self.plows[i];
                p.t += dt;
                let prev = p.x - PLOW_BLADE;
                p.x -= PLOW_SPEED * dt;
                (p.key, p.left, p.width, p.top, prev, p.x - PLOW_BLADE, p.x, p.x_end)
            };

            // 1) clear the columns the blade just passed
            let mut cleared = 0.0f32;
            if let Some(prof) = self.piles.get_mut(&key) {
                let lo = ((now - left as f32).floor() as i32).max(0);
                let hi = ((prev - left as f32).ceil() as i32).min(width).min(prof.len() as i32);
                for c in lo..hi {
                    cleared += prof[c as usize];
                    prof[c as usize] = 0.0;
                }
            }
            self.plows[i].carry += cleared;
            while self.plows[i].carry >= PLOW_SPRAY {
                self.plows[i].carry -= PLOW_SPRAY;
                if self.chunks.len() >= CHUNK_MAX * 2 {
                    continue;
                }
                let cr = ((PLOW_SPRAY / std::f32::consts::PI).sqrt() * 1.3).clamp(1.5, 9.0);
                self.chunks.push(Chunk {
                    x: now,
                    y: top as f32 - 6.0 - self.rng.next_f32() * 8.0,
                    vx: -(PLOW_SPEED * 0.4 + self.rng.next_f32() * 120.0),
                    vy: -(60.0 + self.rng.next_f32() * 150.0),
                    vol: PLOW_SPRAY,
                    radius: cr,
                    age: -0.8, // thrown snow flies on, it does not settle right behind the blade
                    rect: (0, 0, 0, 0),
                });
            }

            // 2) balls / snowmen standing on this edge that the blade reaches
            let mut dead: Vec<u32> = Vec::new();
            for b in &self.balls {
                if let Some(Rest::Surface { key: k, .. }) = b.rest {
                    let m = (b.r() * 0.6).max(6.0);
                    if k == key && b.x >= now - m && b.x <= prev + m {
                        dead.push(b.id);
                    }
                }
            }
            if !dead.is_empty() {
                let n0 = self.chunks.len();
                self.kill_balls(dead);
                for c in self.chunks[n0..].iter_mut() {
                    c.age = -0.8;
                    c.vx -= 100.0;
                }
            }

            // 3) off the left end: done
            if x < x_end {
                let p = self.plows.remove(i);
                if p.rect.2 > p.rect.0 {
                    self.dead_rects.push(p.rect);
                }
            } else {
                i += 1;
            }
        }
    }

    /// LMB pressed at (px, py). Returns true if the click was used (and must not reach other windows).
    fn on_mouse_down(&mut self, px: i32, py: i32) -> bool {
        if self.paused {
            return false;
        }
        self.release(); // a stale held ball (missed button-up) is let go first
        let (fx, fy) = (px as f32, py as f32);

        // 1) pick up a loose ball (not a finished snowman, nothing standing on it)
        for i in 0..self.balls.len() {
            let b = &self.balls[i];
            if b.mode != Mode::Resting || b.snowman || self.has_child(b.id) {
                continue;
            }
            let (dx, dy) = (fx - b.x, fy - b.y);
            if dx * dx + dy * dy <= (b.r() + 3.0) * (b.r() + 3.0) {
                let b = &mut self.balls[i];
                b.mode = Mode::Held;
                b.rest = None;
                b.vy = 0.0;
                return true;
            }
        }

        // 2) start a new ball from a snow pile
        for s in &self.surfaces {
            if px < s.left || px >= s.left + s.width {
                continue;
            }
            if !s.segs.iter().any(|&(a, b)| px >= a && px < b) {
                continue;
            }
            let Some(prof) = self.piles.get_mut(&s.key) else { continue };
            if prof.is_empty() {
                continue;
            }
            let col = (px - s.left) as usize;
            if col >= prof.len() {
                continue;
            }
            let last = prof.len() - 1;
            let h = prof[col.saturating_sub(3)..=(col + 3).min(last)]
                .iter()
                .cloned()
                .fold(0.0f32, f32::max);
            if h < 1.0 || py >= s.top || fy < s.top as f32 - h - 5.0 {
                continue;
            }
            // scoop the first handful of snow
            let (c0, c1) = (col.saturating_sub(8), (col + 8).min(last));
            let avail: f32 = prof[c0..=c1].iter().sum();
            let take = avail.min(BALL_START_VOL);
            if avail > 0.0 {
                let sc = take / avail;
                for v in &mut prof[c0..=c1] {
                    *v -= *v * sc;
                }
            }
            self.next_ball += 1;
            self.balls.push(Ball {
                id: self.next_ball,
                x: fx,
                y: fy,
                vy: 0.0,
                vol: take.max(8.0),
                mode: Mode::Held,
                rest: None,
                snowman: false,
                face: false,
                rect: (0, 0, 0, 0),
            });
            return true;
        }
        false
    }

    /// LMB released. Returns true if a held ball was let go.
    fn on_mouse_up(&mut self) -> bool {
        self.release()
    }

    /// Let go of the held ball: it drops onto a support, or shatters if there is none.
    fn release(&mut self) -> bool {
        let Some(i) = self.balls.iter().position(|b| b.mode == Mode::Held) else {
            return false;
        };
        match self.find_support(i) {
            Some(rest) => {
                let b = &mut self.balls[i];
                b.mode = Mode::Falling;
                b.rest = Some(rest);
                b.vy = 0.0;
            }
            None => self.drop_ball(i),
        }
        true
    }

    /// Closest thing under ball `i` that it can stand on.
    fn find_support(&self, i: usize) -> Option<Rest> {
        let b = &self.balls[i];
        let r = b.r();
        let mut best: Option<(f32, Rest)> = None;

        // on top of another ball
        for o in &self.balls {
            if o.id == b.id || o.mode != Mode::Resting || o.snowman || self.has_child(o.id) {
                continue;
            }
            let or = o.r();
            if (b.x - o.x).abs() > or || b.y > o.y {
                continue;
            }
            let gap = (o.y - or) - (b.y + r);
            if gap > BALL_SNAP {
                continue;
            }
            if best.map_or(true, |(d, _)| gap.abs() < d) {
                best = Some((gap.abs(), Rest::Ball(o.id)));
            }
        }

        // on the top edge of a window / the taskbar
        for s in &self.surfaces {
            if b.x < s.left as f32 || b.x >= (s.left + s.width) as f32 {
                continue;
            }
            if !s.segs.iter().any(|&(a, c)| b.x >= a as f32 && b.x < c as f32) {
                continue;
            }
            let gap = s.top as f32 - (b.y + r);
            if gap > BALL_SNAP || gap < -(r + 10.0) {
                continue;
            }
            if best.map_or(true, |(d, _)| gap.abs() < d) {
                best = Some((
                    gap.abs(),
                    Rest::Surface { key: s.key, top: s.top, left: s.left, width: s.width },
                ));
            }
        }
        best.map(|(_, r)| r)
    }

    /// The held ball follows the cursor and scoops up snow it is touching.
    fn update_held(&mut self, dt: f32) {
        let Some(i) = self.balls.iter().position(|b| b.mode == Mode::Held) else { return };
        let mut pt = POINT::default();
        unsafe {
            let _ = GetCursorPos(&mut pt);
        }
        let k = 1.0 - (-35.0 * dt).exp();
        let (sw, sh) = (self.w as f32, self.h as f32);
        let b = &mut self.balls[i];
        b.x = (b.x + (pt.x as f32 - b.x) * k).clamp(0.0, sw - 1.0);
        b.y = (b.y + (pt.y as f32 - b.y) * k).clamp(0.0, sh - 1.0);
        let r = b.r();
        if r >= BALL_MAX_R {
            return;
        }
        for s in &self.surfaces {
            if b.x < s.left as f32 || b.x >= (s.left + s.width) as f32 {
                continue;
            }
            let top = s.top as f32;
            if b.y + r < top - s.max_h - 8.0 || b.y - r > top + 2.0 {
                continue; // not touching the snow of this edge
            }
            let Some(prof) = self.piles.get_mut(&s.key) else { continue };
            if prof.is_empty() {
                continue;
            }
            let reach = r * 1.4 + 8.0;
            let c0 = ((b.x - reach) as i32 - s.left).max(0) as usize;
            let c1 = (((b.x + reach) as i32 - s.left).min(prof.len() as i32 - 1)).max(0) as usize;
            if c0 > c1 {
                break;
            }
            let avail: f32 = prof[c0..=c1].iter().sum();
            let take = (BALL_GATHER * dt).min(avail).min(BALL_MAX_VOL - b.vol);
            if take <= 0.0 {
                break;
            }
            let sc = take / avail;
            for v in &mut prof[c0..=c1] {
                *v -= *v * sc;
            }
            b.vol += take;
            break;
        }
    }

    /// Falling balls drop onto their support, resting balls follow it (pile height, ball below).
    fn update_balls(&mut self, dt: f32) {
        let snap: Vec<(u32, f32, f32, f32)> =
            self.balls.iter().map(|b| (b.id, b.x, b.y, b.r())).collect();
        let ease = 1.0 - (-18.0 * dt).exp();
        for b in self.balls.iter_mut() {
            if b.mode == Mode::Held {
                continue;
            }
            let r = b.r();
            let target = match b.rest {
                Some(Rest::Surface { key, .. }) => {
                    let mut t = None;
                    for s in &self.surfaces {
                        if s.key != key {
                            continue;
                        }
                        let col = (b.x as i32 - s.left).clamp(0, s.width - 1) as usize;
                        let h = match self.piles.get(&key) {
                            Some(p) => p.get(col).copied().unwrap_or(0.0),
                            None => 0.0,
                        };
                        t = Some((b.x, s.top as f32 - h * 0.5 - r + 1.0));
                        break;
                    }
                    t
                }
                Some(Rest::Ball(id)) => snap
                    .iter()
                    .find(|t| t.0 == id)
                    .map(|&(_, lx, ly, lr)| (lx, ly - lr - r + r.min(lr) * 0.2)),
                None => None,
            };
            let Some((tx, ty)) = target else { continue };
            b.x += (tx - b.x) * ease;
            if b.mode == Mode::Falling {
                b.vy = (b.vy + GRAVITY * dt).min(FALL_MAX);
                b.y += b.vy * dt;
                if b.y >= ty {
                    b.y = ty;
                    b.vy = 0.0;
                    b.mode = Mode::Resting;
                }
            } else {
                b.y = ty;
            }
        }
    }

    /// Three balls stacked on a window / the taskbar make a snowman.
    fn update_snowmen(&mut self) {
        let mut found: Vec<(usize, usize, usize)> = Vec::new();
        for (bi, base) in self.balls.iter().enumerate() {
            if base.mode != Mode::Resting
                || base.snowman
                || !matches!(base.rest, Some(Rest::Surface { .. }))
            {
                continue;
            }
            let Some(mi) = self
                .balls
                .iter()
                .position(|c| c.mode == Mode::Resting && c.rest == Some(Rest::Ball(base.id)))
            else {
                continue;
            };
            let mid_id = self.balls[mi].id;
            let Some(ti) = self
                .balls
                .iter()
                .position(|c| c.mode == Mode::Resting && c.rest == Some(Rest::Ball(mid_id)))
            else {
                continue;
            };
            found.push((bi, mi, ti));
        }
        for (bi, mi, ti) in found {
            self.balls[bi].snowman = true;
            self.balls[mi].snowman = true;
            self.balls[ti].snowman = true;
            self.balls[ti].face = true;
        }
    }

    fn frame(&mut self) {
        let now = Instant::now();
        let dt = now.duration_since(self.last).as_secs_f32().min(0.1); // protect against spikes
        self.last = now;

        if self.force_scan || now.duration_since(self.last_scan).as_millis() >= SCAN_MS {
            self.rescan();
            self.last_scan = now;
            self.force_scan = false;
        }

        // 1) erase only the small rects drawn last frame (flakes + piles)
        for f in &self.flakes {
            let (x0, y0, x1, y1) = f.rect;
            for y in y0..y1 {
                unsafe {
                    std::ptr::write_bytes(
                        self.bits.add((y * self.w + x0) as usize),
                        0,
                        (x1 - x0) as usize,
                    );
                }
            }
        }
        for c in &self.chunks {
            let (x0, y0, x1, y1) = c.rect;
            for y in y0..y1 {
                unsafe {
                    std::ptr::write_bytes(
                        self.bits.add((y * self.w + x0) as usize),
                        0,
                        (x1 - x0) as usize,
                    );
                }
            }
        }
        for &(x0, y0, x1, y1) in &self.pile_rects {
            for y in y0..y1 {
                unsafe {
                    std::ptr::write_bytes(
                        self.bits.add((y * self.w + x0) as usize),
                        0,
                        (x1 - x0) as usize,
                    );
                }
            }
        }
        for b in &self.balls {
            clear_rect(self.bits, self.w, b.rect);
        }
        for p in &self.plows {
            clear_rect(self.bits, self.w, p.rect);
        }
        for r in self.dead_rects.drain(..) {
            clear_rect(self.bits, self.w, r);
        }

        // 1b) snowballs: held one follows the cursor, others fall / rest, three in a stack = snowman
        self.update_held(dt);
        self.update_balls(dt);
        self.update_snowmen();
        self.update_plows(dt);
        // lower balls are drawn first so the upper ones overlap them
        self.balls
            .sort_by(|a, b| b.y.partial_cmp(&a.y).unwrap_or(std::cmp::Ordering::Equal));

        // 2) move flakes; a flake that touches a window edge becomes snow
        let (bits, w, h) = (self.bits, self.w, self.h);
        for f in self.flakes.iter_mut() {
            let py = f.y;
            f.y += f.speed * dt;
            f.phase += f.phase_speed * dt;
            let cx = f.x + f.phase.sin() * WIND_SWAY;
            let vol = PILE_RATE * std::f32::consts::PI * f.radius * f.radius;
            if f.y > h as f32 + 10.0
                || try_land(&self.surfaces, &mut self.piles, cx, py, f.y, f.radius, vol)
            {
                f.y = -10.0;
                f.x = self.rng.next_f32() * w as f32;
            }
        }

        // 2b) clumps of snow that fell off windows: gravity, then land on whatever is below
        let mut i = 0;
        while i < self.chunks.len() {
            let c = &mut self.chunks[i];
            c.age += dt;
            c.vy = (c.vy + GRAVITY * dt).min(FALL_MAX);
            let py = c.y;
            c.x += c.vx * dt;
            c.y += c.vy * dt;
            let landed = c.age >= CHUNK_IMMUNE
                && try_land(&self.surfaces, &mut self.piles, c.x, py, c.y, c.radius, c.vol * CHUNK_KEEP);
            let gone = c.y - c.radius > h as f32 || c.x < -50.0 || c.x > w as f32 + 50.0;
            if landed || gone {
                self.chunks.swap_remove(i);
            } else {
                i += 1;
            }
        }

        // 3) piles, then 4) flakes on top
        draw_piles(bits, w, h, &self.surfaces, &self.piles, &mut self.pile_rects);
        for b in self.balls.iter_mut() {
            let r = b.r();
            draw_ball(bits, w, h, b.x, b.y, r, b.face, &mut b.rect);
        }
        for p in self.plows.iter_mut() {
            // draw the truck only where its edge is visible (not under another window)
            let visible = self.surfaces.iter().any(|s| {
                s.key == p.key
                    && s.segs.iter().any(|&(a, b)| p.x >= (a - 40) as f32 && p.x <= (b + 40) as f32)
            });
            if visible {
                draw_plow(bits, w, h, p.x, p.top, p.t, &mut p.rect);
            } else {
                p.rect = (0, 0, 0, 0);
            }
        }
        for f in self.flakes.iter_mut() {
            let cx = f.x + f.phase.sin() * WIND_SWAY;
            draw_blob(bits, w, h, f.radius, f.opacity, &mut f.rect, cx, f.y);
        }
        for c in self.chunks.iter_mut() {
            draw_blob(bits, w, h, c.radius, 0.95, &mut c.rect, c.x, c.y);
        }

        self.present();
    }

    fn present(&self) {
        let size = SIZE { cx: self.w, cy: self.h };
        let src = POINT { x: 0, y: 0 };
        let blend = BLENDFUNCTION {
            BlendOp: AC_SRC_OVER as u8,
            BlendFlags: 0,
            SourceConstantAlpha: 255,
            AlphaFormat: AC_SRC_ALPHA as u8,
        };
        unsafe {
            let _ = UpdateLayeredWindow(
                self.hwnd,
                HDC::default(),
                None,
                Some(&size),
                self.mem_dc,
                Some(&src),
                COLORREF(0),
                Some(&blend),
                ULW_ALPHA,
            );
        }
    }

    /// Pause (hide window + stop timer) while a game / fullscreen video / presentation runs.
    /// NOTE: QUNS_BUSY is deliberately NOT used: our own screen-sized topmost window can
    /// trigger it, which made the snow hide itself and blink. We check the foreground
    /// window ourselves instead (never our own window).
    fn update_pause(&mut self) {
        let want = unsafe {
            let shell = match SHQueryUserNotificationState() {
                Ok(s) => {
                    s == QUNS_RUNNING_D3D_FULL_SCREEN
                        || s == QUNS_PRESENTATION_MODE
                        || s == QUNS_NOT_PRESENT
                }
                Err(_) => false,
            };
            shell || foreground_is_fullscreen(self.hwnd)
        };

        // Hysteresis: change state only after two consecutive identical readings
        if want == self.paused {
            self.streak = 0;
            return;
        }
        self.streak += 1;
        if self.streak < 2 {
            return;
        }
        self.streak = 0;
        let pause = want;
        self.paused = pause;
        unsafe {
            if pause {
                let _ = KillTimer(self.hwnd, TIMER_FRAME);
                let _ = ShowWindow(self.hwnd, SW_HIDE);
            } else {
                self.last = Instant::now();
                self.force_scan = true;
                let _ = ShowWindow(self.hwnd, SW_SHOWNOACTIVATE);
                let _ = SetWindowPos(
                    self.hwnd,
                    HWND_TOPMOST,
                    0,
                    0,
                    0,
                    0,
                    SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE,
                );
                SetTimer(self.hwnd, TIMER_FRAME, 1000 / FPS, None);
            }
        }
    }
}

/// True if the foreground window (not ours, not the desktop/taskbar) covers the whole primary monitor.
unsafe fn foreground_is_fullscreen(own: HWND) -> bool {
    let fg = GetForegroundWindow();
    if fg == HWND::default() || fg == own {
        return false;
    }

    let mut cls = [0u16; 64];
    let n = GetClassNameW(fg, &mut cls).max(0) as usize;
    let name = String::from_utf16_lossy(&cls[..n.min(cls.len())]);
    if matches!(
        name.as_str(),
        "Progman" | "WorkerW" | "Shell_TrayWnd" | "Shell_SecondaryTrayWnd"
    ) {
        return false;
    }

    let mut r = RECT::default();
    if GetWindowRect(fg, &mut r).is_err() {
        return false;
    }
    let mon = MonitorFromWindow(fg, MONITOR_DEFAULTTONEAREST);
    let mut mi = MONITORINFO {
        cbSize: std::mem::size_of::<MONITORINFO>() as u32,
        ..Default::default()
    };
    if !GetMonitorInfoW(mon, &mut mi).as_bool() {
        return false;
    }
    let m = mi.rcMonitor;
    let primary = mi.dwFlags & 1 != 0; // MONITORINFOF_PRIMARY: only the monitor with the snow matters
    primary && r.left <= m.left && r.top <= m.top && r.right >= m.right && r.bottom >= m.bottom
}

unsafe extern "system" fn enum_proc(hwnd: HWND, lparam: LPARAM) -> BOOL {
    let list = &mut *(lparam.0 as *mut Vec<HWND>);
    list.push(hwnd);
    BOOL(1)
}

unsafe fn class_name(hwnd: HWND) -> String {
    let mut cls = [0u16; 64];
    let n = GetClassNameW(hwnd, &mut cls).max(0) as usize;
    String::from_utf16_lossy(&cls[..n.min(cls.len())])
}

/// Describe a top-level window; None if it is not really visible on screen.
/// `surface` = snow may rest on its top edge (normal, non-fullscreen window or the taskbar).
unsafe fn window_info(hwnd: HWND, own: HWND, sw: i32, sh: i32) -> Option<Win> {
    if hwnd == own || !IsWindowVisible(hwnd).as_bool() || IsIconic(hwnd).as_bool() {
        return None;
    }
    // hidden UWP / other-virtual-desktop windows are "visible" but cloaked
    let mut cloaked: u32 = 0;
    if DwmGetWindowAttribute(hwnd, DWMWA_CLOAKED, &mut cloaked as *mut u32 as *mut c_void, 4)
        .is_ok()
        && cloaked != 0
    {
        return None;
    }
    let ex = GetWindowLongW(hwnd, GWL_EXSTYLE) as u32;
    if ex & WS_EX_TRANSPARENT.0 != 0 {
        return None; // click-through overlays (like ours)
    }
    let class = class_name(hwnd);
    if class == "Progman" || class == "WorkerW" {
        return None; // desktop
    }
    let taskbar = class == "Shell_TrayWnd";

    // Visible frame, without the invisible resize borders of Win10/11 windows
    let mut r = RECT::default();
    let ok = DwmGetWindowAttribute(
        hwnd,
        DWMWA_EXTENDED_FRAME_BOUNDS,
        &mut r as *mut RECT as *mut c_void,
        std::mem::size_of::<RECT>() as u32,
    )
    .is_ok();
    if !ok && GetWindowRect(hwnd, &mut r).is_err() {
        return None;
    }
    let (wd, ht) = (r.right - r.left, r.bottom - r.top);
    if wd <= 0 || ht <= 0 || r.right <= 0 || r.bottom <= 0 || r.left >= sw || r.top >= sh {
        return None;
    }

    let fullscreen = r.left <= 0 && r.top <= 0 && r.right >= sw && r.bottom >= sh;
    let has_title = GetWindowTextLengthW(hwnd) > 0;
    let tool = ex & WS_EX_TOOLWINDOW.0 != 0;
    let surface = !fullscreen
        && wd >= MIN_WIN_W
        && ht >= MIN_WIN_H
        && r.top > 20 // maximized windows have their edge off the top of the screen
        && r.top < sh - 4 // auto-hidden taskbar
        && (taskbar || (has_title && !tool));

    Some(Win {
        key: hwnd.0 as isize,
        l: r.left,
        t: r.top,
        r: r.right,
        b: r.bottom,
        surface,
        taskbar,
    })
}

/// Remove [bl, br) from a list of x-spans.
fn subtract(segs: Vec<(i32, i32)>, bl: i32, br: i32) -> Vec<(i32, i32)> {
    let mut out = Vec::with_capacity(segs.len() + 1);
    for (a, b) in segs {
        if br <= a || bl >= b {
            out.push((a, b));
        } else {
            if bl > a {
                out.push((a, bl));
            }
            if br < b {
                out.push((br, b));
            }
        }
    }
    out
}

/// If the flake touches the snow surface of a visible window edge, add its volume
/// to that pile and return true (the flake is consumed).
fn try_land(
    surfaces: &[Surface],
    piles: &mut HashMap<isize, Vec<f32>>,
    cx: f32,
    py: f32, // y before this frame's move: lets fast clumps not tunnel through an edge
    cy: f32,
    r: f32,
    vol: f32,
) -> bool {
    for s in surfaces {
        let top = s.top as f32;
        if py >= top || cx < s.left as f32 || cx >= (s.left + s.width) as f32 {
            continue; // already below the edge / not above this window
        }
        if !s.segs.iter().any(|&(a, b)| cx >= a as f32 && cx < b as f32) {
            continue; // that part of the edge is covered by another window
        }
        let Some(prof) = piles.get_mut(&s.key) else { continue };
        let col = (cx as i32 - s.left) as usize;
        if col >= prof.len() {
            continue;
        }
        if cy + r >= top - prof[col] {
            deposit(prof, col, r, vol, s.max_h, s.left, &s.segs);
            return true;
        }
    }
    false
}

/// Turn the snow of columns `prof` (relative to surface `o`, old geometry) into falling clumps.
/// Only snow on the visible parts of the edge is shown falling.
fn spawn_chunks(chunks: &mut Vec<Chunk>, rng: &mut Rng, o: &Surface, prof: &[f32]) {
    let step = CHUNK_COLS.max(o.width / 160).max(1) as usize; // wide windows -> bigger clumps
    let n = prof.len();
    let mut j = 0;
    while j < n {
        let (j0, j1) = (j, (j + step).min(n));
        j = j1;
        let mut vol = 0.0f32;
        for c in j0..j1 {
            let x = o.left + c as i32;
            if prof[c] > 0.0 && o.segs.iter().any(|&(a, b)| x >= a && x < b) {
                vol += prof[c];
            }
        }
        if vol < 1.5 || chunks.len() >= CHUNK_MAX {
            continue;
        }
        let avg = vol / (j1 - j0) as f32;
        let r = ((vol / std::f32::consts::PI).sqrt() * 1.3).clamp(1.5, 9.0);
        chunks.push(Chunk {
            x: o.left as f32 + (j0 + j1) as f32 * 0.5,
            y: o.top as f32 - avg * 0.5,
            vx: (rng.next_f32() - 0.5) * 80.0,
            vy: rng.next_f32() * 60.0,
            vol,
            radius: r,
            age: 0.0,
            rect: (0, 0, 0, 0),
        });
    }
}

fn deposit(
    prof: &mut [f32],
    col: usize,
    r: f32,
    vol: f32,
    max_h: f32,
    left: i32,
    segs: &[(i32, i32)],
) {
    // covered parts of the edge are walls: no snow lands there and none flows into them,
    // so the free parts fill up as if they were the whole edge
    let vis = |c: usize| {
        let x = left + c as i32;
        segs.iter().any(|&(a, b)| x >= a && x < b)
    };
    let k = (r * 2.0).ceil() as i32 + 1;
    let n = prof.len() as i32;
    // triangular blob of snow around the landing point
    for dc in -k..=k {
        let c = col as i32 + dc;
        if c < 0 || c >= n || !vis(c as usize) {
            continue;
        }
        let wgt = 1.0 - dc.abs() as f32 / (k as f32 + 1.0);
        prof[c as usize] += vol * wgt / (k as f32 + 1.0);
    }
    // relax: soften spikes so the pile looks like snow, not needles
    let lo = (col as i32 - k - 4).max(0) as usize;
    let hi = (col as i32 + k + 4).min(n - 1).max(0) as usize;
    for _ in 0..3 {
        for i in lo..hi {
            if !vis(i) || !vis(i + 1) {
                continue;
            }
            let d = prof[i] - prof[i + 1];
            if d.abs() > PILE_SLOPE {
                let t = (d.abs() - PILE_SLOPE) * 0.5;
                if d > 0.0 {
                    prof[i] -= t;
                    prof[i + 1] += t;
                } else {
                    prof[i] += t;
                    prof[i + 1] -= t;
                }
            }
        }
    }
    for c in lo..=hi {
        if prof[c] > max_h {
            prof[c] = max_h;
        }
    }
}

#[inline]
fn put(bits: *mut u32, w: i32, h: i32, x: i32, y: i32, a: u32) {
    if x < 0 || y < 0 || x >= w || y >= h {
        return;
    }
    unsafe { *bits.add((y * w + x) as usize) = a * 0x0101_0101 };
}

/// Draw the snow lying on the visible parts of window top edges.
fn draw_piles(
    bits: *mut u32,
    sw: i32,
    sh: i32,
    surfaces: &[Surface],
    piles: &HashMap<isize, Vec<f32>>,
    rects: &mut Vec<(i32, i32, i32, i32)>,
) {
    rects.clear();
    for s in surfaces {
        let Some(prof) = piles.get(&s.key) else { continue };
        if prof.is_empty() {
            continue;
        }
        let y_min = (s.top - s.max_h.ceil() as i32 - 2).max(0);
        let y_max = s.top.min(sh);
        for &(a, b) in &s.segs {
            let (a, b) = (a.max(0), b.min(sw));
            if a >= b || y_min >= y_max {
                continue;
            }
            rects.push((a, y_min, b, y_max));
            for x in a..b {
                let rel = (x - s.left) as usize;
                if rel >= prof.len() {
                    continue;
                }
                // snow thins out toward the window corners
                let edge = rel.min(prof.len() - 1 - rel) as f32;
                let hh = prof[rel] * ((edge + 1.0) / 6.0).min(1.0);
                if hh < 0.25 {
                    continue;
                }
                let full = hh.floor() as i32;
                let frac = hh - full as f32;
                for i in 1..=full {
                    put(bits, sw, sh, x, s.top - i, PILE_ALPHA as u32);
                }
                if frac > 0.1 {
                    put(bits, sw, sh, x, s.top - full - 1, (frac * PILE_ALPHA) as u32);
                }
            }
        }
    }
}

/// Soft white blob (radial gradient white -> transparent), premultiplied alpha,
/// drawn analytically at a sub-pixel position so slow flakes move smoothly.
#[allow(clippy::too_many_arguments)]
fn draw_blob(
    bits: *mut u32,
    w: i32,
    h: i32,
    r: f32,
    opacity: f32,
    rect: &mut (i32, i32, i32, i32),
    cx: f32,
    cy: f32,
) {
    let x0 = ((cx - r).floor() as i32).max(0);
    let y0 = ((cy - r).floor() as i32).max(0);
    let x1 = ((cx + r).ceil() as i32 + 1).min(w);
    let y1 = ((cy + r).ceil() as i32 + 1).min(h);
    if x0 >= x1 || y0 >= y1 {
        *rect = (0, 0, 0, 0);
        return;
    }
    for py in y0..y1 {
        let dy = py as f32 + 0.5 - cy;
        for px in x0..x1 {
            let dx = px as f32 + 0.5 - cx;
            let t = (dx * dx + dy * dy).sqrt() / r;
            if t >= 1.0 {
                continue;
            }
            let profile = if t < 0.5 { 255.0 - t * 110.0 } else { 200.0 - (t - 0.5) * 400.0 };
            let sa = (profile * opacity) as u32; // 0..255
            blend_at(bits, w, h, px, py, (255, 255, 255), sa);
        }
    }
    *rect = (x0, y0, x1, y1);
}

fn clear_rect(bits: *mut u32, w: i32, rect: (i32, i32, i32, i32)) {
    let (x0, y0, x1, y1) = rect;
    for y in y0..y1 {
        unsafe {
            std::ptr::write_bytes(bits.add((y * w + x0) as usize), 0, (x1 - x0) as usize);
        }
    }
}

/// Source-over blend of a non-premultiplied colour with alpha `a` onto a premultiplied pixel.
#[inline]
fn blend_at(bits: *mut u32, w: i32, h: i32, x: i32, y: i32, rgb: (u32, u32, u32), a: u32) {
    if a == 0 || x < 0 || y < 0 || x >= w || y >= h {
        return;
    }
    let a = a.min(255);
    unsafe {
        let p = bits.add((y * w + x) as usize);
        let d = *p;
        let ia = 255 - a;
        let oa = (a + (d >> 24) * ia / 255).min(255);
        let or = (rgb.0 * a / 255 + ((d >> 16) & 0xFF) * ia / 255).min(255);
        let og = (rgb.1 * a / 255 + ((d >> 8) & 0xFF) * ia / 255).min(255);
        let ob = (rgb.2 * a / 255 + (d & 0xFF) * ia / 255).min(255);
        *p = (oa << 24) | (or << 16) | (og << 8) | ob;
    }
}

fn fill_circle(bits: *mut u32, w: i32, h: i32, cx: f32, cy: f32, rad: f32, rgb: (u32, u32, u32)) {
    let (x0, x1) = ((cx - rad - 1.0).floor() as i32, (cx + rad + 1.0).ceil() as i32);
    let (y0, y1) = ((cy - rad - 1.0).floor() as i32, (cy + rad + 1.0).ceil() as i32);
    for py in y0..=y1 {
        for px in x0..=x1 {
            let (dx, dy) = (px as f32 + 0.5 - cx, py as f32 + 0.5 - cy);
            let cov = (rad - (dx * dx + dy * dy).sqrt() + 0.5).clamp(0.0, 1.0);
            blend_at(bits, w, h, px, py, rgb, (cov * 255.0) as u32);
        }
    }
}

/// A ball falls apart into many small clumps of the snow it was made of.
fn shatter(chunks: &mut Vec<Chunk>, rng: &mut Rng, cx: f32, cy: f32, r: f32, vol: f32) {
    let n = ((vol / 15.0) as usize).clamp(6, 60);
    let each = vol / n as f32;
    let cr = ((each / std::f32::consts::PI).sqrt() * 1.3).clamp(1.5, 9.0);
    let r = r.max(1.0);
    for _ in 0..n {
        if chunks.len() >= CHUNK_MAX * 2 {
            break;
        }
        let a = rng.next_f32() * std::f32::consts::TAU;
        let d = r * rng.next_f32().sqrt();
        let (dx, dy) = (a.cos() * d, a.sin() * d);
        chunks.push(Chunk {
            x: cx + dx,
            y: cy + dy,
            vx: dx / r * 90.0 + (rng.next_f32() - 0.5) * 40.0,
            vy: dy / r * 90.0 - rng.next_f32() * 90.0,
            vol: each,
            radius: cr,
            age: 0.0,
            rect: (0, 0, 0, 0),
        });
    }
}

/// A shaded snowball; with `face` it is a snowman's head: coal eyes and mouth, carrot nose.
#[allow(clippy::too_many_arguments)]
fn draw_ball(
    bits: *mut u32,
    w: i32,
    h: i32,
    cx: f32,
    cy: f32,
    r: f32,
    face: bool,
    rect: &mut (i32, i32, i32, i32),
) {
    let x0 = ((cx - r).floor() as i32 - 1).max(0);
    let y0 = ((cy - r).floor() as i32 - 1).max(0);
    let x1 = ((cx + r).ceil() as i32 + 2).min(w);
    let y1 = ((cy + r).ceil() as i32 + 2).min(h);
    if x0 >= x1 || y0 >= y1 {
        *rect = (0, 0, 0, 0);
        return;
    }
    *rect = (x0, y0, x1, y1);

    const LIGHT: (f32, f32, f32) = (-0.45, -0.60, 0.66); // from the top-left, towards the viewer
    const SHADE: (f32, f32, f32) = (168.0, 190.0, 222.0); // bluish shadow
    const RIM: (f32, f32, f32) = (140.0, 165.0, 200.0); // thin outline so it stays visible on white
    for py in y0..y1 {
        for px in x0..x1 {
            let (dx, dy) = (px as f32 + 0.5 - cx, py as f32 + 0.5 - cy);
            let d = (dx * dx + dy * dy).sqrt();
            let cov = (r - d + 0.5).clamp(0.0, 1.0);
            if cov <= 0.0 {
                continue;
            }
            let (nx, ny) = (dx / r, dy / r);
            let nz = (1.0 - nx * nx - ny * ny).max(0.0).sqrt();
            let lum = (nx * LIGHT.0 + ny * LIGHT.1 + nz * LIGHT.2).max(0.0);
            let t = 0.35 + 0.65 * lum;
            let rim = ((d - (r - 1.5)) / 1.5).clamp(0.0, 1.0) * 0.55;
            let mix = |sh: f32, ri: f32| {
                let base = sh + (255.0 - sh) * t;
                (base + (ri - base) * rim) as u32
            };
            blend_at(
                bits,
                w,
                h,
                px,
                py,
                (mix(SHADE.0, RIM.0), mix(SHADE.1, RIM.1), mix(SHADE.2, RIM.2)),
                (cov * 255.0) as u32,
            );
        }
    }

    if !face {
        return;
    }
    let coal = (28, 28, 32);
    // eyes
    let eye = (r * 0.11).max(1.3);
    fill_circle(bits, w, h, cx - r * 0.34, cy - r * 0.22, eye, coal);
    fill_circle(bits, w, h, cx + r * 0.34, cy - r * 0.22, eye, coal);
    // mouth: a smile of five coals
    let peb = (r * 0.075).max(1.1);
    for i in 0..5 {
        let a = std::f32::consts::PI * (0.22 + 0.56 * i as f32 / 4.0);
        fill_circle(
            bits,
            w,
            h,
            cx + a.cos() * r * 0.55,
            cy + r * 0.12 + a.sin() * r * 0.55,
            peb,
            coal,
        );
    }
    // carrot nose pointing sideways, slightly down
    let (sx, sy) = (cx - r * 0.05, cy + r * 0.06);
    let len = r;
    let hw = (r * 0.14).max(1.4);
    for px in (sx.floor() as i32)..((sx + len).ceil() as i32) {
        let t = ((px as f32 + 0.5 - sx) / len).clamp(0.0, 1.0);
        let half = hw * (1.0 - t) + 0.35;
        let yc = sy + t * r * 0.12;
        for py in ((yc - half).floor() as i32)..=((yc + half).ceil() as i32) {
            let off = py as f32 + 0.5 - yc;
            let cov = (half - off.abs() + 0.5).clamp(0.0, 1.0);
            let k = ((off + half) / (2.0 * half)).clamp(0.0, 1.0); // top light, bottom darker
            let col = (
                (245.0 - 45.0 * k) as u32,
                (135.0 - 45.0 * k) as u32,
                (25.0 - 15.0 * k) as u32,
            );
            blend_at(bits, w, h, px, py, col, (cov * 255.0) as u32);
        }
    }
}

fn fill_rect(
    bits: *mut u32,
    w: i32,
    h: i32,
    x0: i32,
    y0: i32,
    x1: i32,
    y1: i32,
    rgb: (u32, u32, u32),
) {
    for y in y0..y1 {
        for x in x0..x1 {
            blend_at(bits, w, h, x, y, rgb, 255);
        }
    }
}

/// Snowplow truck seen from the side, driving to the left; wheels stand on y = `base`.
fn draw_plow(
    bits: *mut u32,
    w: i32,
    h: i32,
    cx: f32,
    base: i32,
    t: f32,
    rect: &mut (i32, i32, i32, i32),
) {
    let (ox, oy) = (cx.round() as i32, base);
    let (x0, x1) = ((ox - 46).max(0), (ox + 36).min(w));
    let (y0, y1) = ((oy - 34).max(0), (oy + 2).min(h));
    if x0 >= x1 || y0 >= y1 {
        *rect = (0, 0, 0, 0);
        return;
    }
    *rect = (x0, y0, x1, y1);

    const YELLOW: (u32, u32, u32) = (250, 190, 30);
    const ORANGE: (u32, u32, u32) = (235, 120, 20);
    const DARK: (u32, u32, u32) = (50, 52, 58);
    const STEEL: (u32, u32, u32) = (160, 168, 178);
    const GLASS: (u32, u32, u32) = (150, 205, 235);
    let r = |ax: i32, ay: i32, bx: i32, by: i32, c: (u32, u32, u32)| {
        fill_rect(bits, w, h, ox + ax, oy + ay, ox + bx, oy + by, c)
    };

    r(-28, -11, 31, -6, DARK); // chassis
    r(-4, -19, 31, -11, ORANGE); // hopper
    r(-4, -19, 31, -17, (200, 95, 10));
    r(-27, -27, -5, -11, YELLOW); // cab
    r(-28, -28, -4, -26, (225, 165, 15));
    r(-25, -24, -9, -15, GLASS);
    r(-17, -24, -16, -15, YELLOW);
    r(-29, -15, -27, -12, (255, 245, 170)); // headlight
    r(-29, -8, -27, -5, (60, 60, 66)); // bumper
    // blade on its arm, leaning back at the top
    r(-37, -9, -28, -7, DARK);
    for hh in 0..19 {
        let xl = -41 + (hh * 2) / 9;
        let c = if hh >= 17 { (205, 212, 222) } else { STEEL };
        r(xl, -hh - 1, xl + 4, -hh, c);
    }
    // wheels
    for wx in [-17, 19] {
        fill_circle(bits, w, h, (ox + wx) as f32, (oy - 6) as f32, 6.0, (30, 30, 34));
        fill_circle(bits, w, h, (ox + wx) as f32, (oy - 6) as f32, 2.5, (175, 178, 185));
    }
    // flashing beacon
    r(-18, -28, -12, -27, DARK);
    let on = (t * 4.0) as i32 % 2 == 0;
    r(-17, -31, -13, -28, if on { (255, 200, 0) } else { (130, 90, 0) });
}

/// Global low-level mouse hook: lets the overlay catch LMB presses on snow (and swallow them)
/// while every other click still goes to the windows underneath.
unsafe extern "system" fn mouse_proc(code: i32, wparam: WPARAM, lparam: LPARAM) -> LRESULT {
    if code >= 0 {
        if let Some(s) = STATE.load(AtomicOrdering::Relaxed).as_mut() {
            let info = &*(lparam.0 as *const MSLLHOOKSTRUCT);
            match wparam.0 as u32 {
                WM_LBUTTONDOWN => {
                    if s.on_mouse_down(info.pt.x, info.pt.y) {
                        return LRESULT(1);
                    }
                }
                WM_LBUTTONUP => {
                    if s.on_mouse_up() {
                        return LRESULT(1);
                    }
                }
                _ => {}
            }
        }
    }
    CallNextHookEx(HHOOK::default(), code, wparam, lparam)
}

fn remove_tray(hwnd: HWND) {
    let nid = NOTIFYICONDATAW {
        cbSize: std::mem::size_of::<NOTIFYICONDATAW>() as u32,
        hWnd: hwnd,
        uID: 1,
        ..Default::default()
    };
    unsafe {
        let _ = Shell_NotifyIconW(NIM_DELETE, &nid);
    }
}

fn add_tray(hwnd: HWND) {
    let mut nid = NOTIFYICONDATAW {
        cbSize: std::mem::size_of::<NOTIFYICONDATAW>() as u32,
        hWnd: hwnd,
        uID: 1,
        uFlags: NIF_ICON | NIF_MESSAGE | NIF_TIP,
        uCallbackMessage: WM_TRAY,
        ..Default::default()
    };
    unsafe {
        if let Ok(icon) = LoadImageW(
            GetModuleHandleW(None).unwrap_or_default(),
            PCWSTR(1usize as *const u16),
            IMAGE_ICON,
            16,
            16,
            LR_DEFAULTCOLOR,
        ) {
            nid.hIcon = HICON(icon.0);
        }
    }
    for (i, c) in "Snow".encode_utf16().enumerate() {
        nid.szTip[i] = c;
    }
    unsafe {
        let _ = Shell_NotifyIconW(NIM_ADD, &nid);
    }
}

fn show_menu(hwnd: HWND) {
    unsafe {
        let Ok(menu) = CreatePopupMenu() else { return };
        let _ = AppendMenuW(menu, MF_STRING, ID_CLOSE, w!("Close"));
        let mut pt = POINT::default();
        let _ = GetCursorPos(&mut pt);
        let _ = SetForegroundWindow(hwnd); // required so the menu closes when clicking elsewhere
        let _ = TrackPopupMenu(menu, TPM_RIGHTBUTTON, pt.x, pt.y, 0, hwnd, None);
        let _ = PostMessageW(hwnd, WM_NULL, WPARAM(0), LPARAM(0));
        let _ = DestroyMenu(menu);
    }
}

unsafe extern "system" fn wndproc(hwnd: HWND, msg: u32, wparam: WPARAM, lparam: LPARAM) -> LRESULT {
    match msg {
        WM_TIMER => {
            let state = GetWindowLongPtrW(hwnd, GWLP_USERDATA) as *mut State;
            if let Some(s) = state.as_mut() {
                match wparam.0 {
                    TIMER_FRAME => s.frame(),
                    TIMER_WATCH => s.update_pause(),
                    _ => {}
                }
            }
            LRESULT(0)
        }
        WM_TRAY => {
            if (lparam.0 as u32 & 0xFFFF) == WM_RBUTTONUP {
                show_menu(hwnd);
            }
            LRESULT(0)
        }
        WM_COMMAND => {
            if (wparam.0 & 0xFFFF) == ID_CLOSE {
                let _ = DestroyWindow(hwnd);
            }
            LRESULT(0)
        }
        WM_DESTROY => {
            remove_tray(hwnd);
            PostQuitMessage(0);
            LRESULT(0)
        }
        _ => DefWindowProcW(hwnd, msg, wparam, lparam),
    }
}

fn main() -> windows::core::Result<()> {
    unsafe {
        // Snow should never compete with real work
        let _ = SetPriorityClass(GetCurrentProcess(), BELOW_NORMAL_PRIORITY_CLASS);
        // Real pixels, no DPI scaling
        let _ = SetProcessDPIAware();

        let hinstance: HINSTANCE = GetModuleHandleW(None)?.into();
        let class_name = w!("SnowOverlayWindow");

        let wc = WNDCLASSW {
            lpfnWndProc: Some(wndproc),
            hInstance: hinstance,
            lpszClassName: class_name,
            ..Default::default()
        };
        RegisterClassW(&wc);

        let w = GetSystemMetrics(SM_CXSCREEN);
        let h = GetSystemMetrics(SM_CYSCREEN);

        let hwnd = CreateWindowExW(
            WS_EX_LAYERED
                | WS_EX_TRANSPARENT // click-through
                | WS_EX_TOPMOST
                | WS_EX_TOOLWINDOW // no taskbar / Alt+Tab
                | WS_EX_NOACTIVATE,
            class_name,
            w!("Snow"),
            WS_POPUP,
            0,
            0,
            w,
            h,
            None,
            None,
            hinstance,
            None,
        )?;

        let icon = LoadImageW(
            hinstance,
            PCWSTR(1usize as *const u16),
            IMAGE_ICON,
            32,
            32,
            LR_DEFAULTCOLOR,
        );

        if let Ok(icon) = icon {
            let _ = SendMessageW(hwnd, WM_SETICON, WPARAM(ICON_BIG as usize), LPARAM(icon.0 as isize));
            let _ = SendMessageW(hwnd, WM_SETICON, WPARAM(ICON_SMALL as usize), LPARAM(icon.0 as isize));
        }

        // One 32-bit top-down DIB for the whole scene
        let mem_dc = CreateCompatibleDC(None);
        let bmi = BITMAPINFO {
            bmiHeader: BITMAPINFOHEADER {
                biSize: std::mem::size_of::<BITMAPINFOHEADER>() as u32,
                biWidth: w,
                biHeight: -h,
                biPlanes: 1,
                biBitCount: 32,
                biCompression: BI_RGB.0,
                ..Default::default()
            },
            ..Default::default()
        };
        let mut bits: *mut c_void = std::ptr::null_mut();
        let bitmap = CreateDIBSection(mem_dc, &bmi, DIB_RGB_COLORS, &mut bits, None, 0)?;
        let old_obj = SelectObject(mem_dc, bitmap);

        let mut rng = Rng::new();
        let flakes = State::new_flakes(&mut rng, w, h);
        let state = Box::into_raw(Box::new(State {
            hwnd,
            mem_dc,
            bitmap,
            old_obj,
            bits: bits as *mut u32,
            w,
            h,
            flakes,
            rng,
            last: Instant::now(),
            paused: false,
            streak: 0,
            surfaces: Vec::new(),
            piles: HashMap::new(),
            pile_rects: Vec::new(),
            last_scan: Instant::now(),
            force_scan: true,
            chunks: Vec::new(),
            balls: Vec::new(),
            next_ball: 0,
            dead_rects: Vec::new(),
            plows: Vec::new(),
        }));
        SetWindowLongPtrW(hwnd, GWLP_USERDATA, state as isize);
        STATE.store(state, AtomicOrdering::SeqCst);
        // Without the hook the snow still works, only snowballs can't be made
        let hook = SetWindowsHookExW(WH_MOUSE_LL, Some(mouse_proc), hinstance, 0).ok();

        add_tray(hwnd);
        (*state).frame(); // first frame
        let _ = ShowWindow(hwnd, SW_SHOWNOACTIVATE);
        SetTimer(hwnd, TIMER_FRAME, 1000 / FPS, None);
        SetTimer(hwnd, TIMER_WATCH, 2000, None);

        // Sleeps here between frames
        let mut msg = MSG::default();
        while GetMessageW(&mut msg, None, 0, 0).as_bool() {
            let _ = TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }

        // Cleanup
        if let Some(hook) = hook {
            let _ = UnhookWindowsHookEx(hook);
        }
        STATE.store(std::ptr::null_mut(), AtomicOrdering::SeqCst);
        let s = Box::from_raw(state);
        SelectObject(s.mem_dc, s.old_obj);
        let _ = DeleteObject(s.bitmap);
        let _ = DeleteDC(s.mem_dc);
    }
    Ok(())
}
import tkinter as tk
from tkinter import ttk, messagebox
import math
import random
import itertools
import time

# --- LOGIKA ALGORYTMÓW KRZYŻOWANIA ---


def pmx(p1, p2):
    size = len(p1)
    a, b = sorted(random.sample(range(size), 2))
    o1 = [-1] * size
    o1[a:b+1] = p1[a:b+1]

    for i in range(a, b+1):
        val2 = p2[i]
        if val2 not in o1:
            curr_idx = i
            while a <= curr_idx <= b:
                mapped_val1 = p1[curr_idx]
                curr_idx = p2.index(mapped_val1)
            o1[curr_idx] = val2

    for i in range(size):
        if o1[i] == -1:
            o1[i] = p2[i]
    return o1


def ox(p1, p2):
    size = len(p1)
    a, b = sorted(random.sample(range(size), 2))
    o1 = [-1] * size
    o1[a:b+1] = p1[a:b+1]

    fill_order = p2[b+1:] + p2[:b+1]
    fill_order = [x for x in fill_order if x not in o1]

    idx_p2 = 0
    for i in range(b+1, b+1+size):
        idx = i % size
        if o1[idx] == -1:
            o1[idx] = fill_order[idx_p2]
            idx_p2 += 1
    return o1


def cx(p1, p2):
    size = len(p1)
    o1 = [-1] * size
    cycle = set()
    idx = 0

    while True:
        cycle.add(idx)
        val1 = p1[idx]
        val2 = p2[idx]
        o1[idx] = val1
        idx = p1.index(val2)
        if idx in cycle:
            break

    for i in range(size):
        if o1[i] == -1:
            o1[i] = p2[i]
    return o1


def erx(p1, p2):
    """
    Edge Recombination Crossover (operator krawedziowy).

    W odroznieniu od PMX/OX/CX, ktore dbaja o pozycje miast, ERX zachowuje
    KRAWEDZIE (sasiedztwa) miedzy miastami - a to one decyduja o dlugosci
    trasy w TSP. Dlatego ERX zwykle daje najlepsze rezultaty dla TSP.
    """
    size = len(p1)

    # 1. Mapa krawedzi (sasiedztwa) z obu rodzicow
    neighbors = {c: set() for c in p1}
    for parent in (p1, p2):
        for i in range(size):
            c = parent[i]
            neighbors[c].add(parent[(i - 1) % size])
            neighbors[c].add(parent[(i + 1) % size])

    # 2. Miasto startowe
    current = random.choice([p1[0], p2[0]])
    child = [current]
    visited = {current}

    while len(child) < size:
        # Usuwamy biezace miasto ze wszystkich list sasiadow
        for nb in neighbors.values():
            nb.discard(current)

        options = neighbors[current]
        if options:
            # 3. Wybor sasiada o najmniejszej liczbie wlasnych sasiadow
            min_count = min(len(neighbors[c]) for c in options)
            candidates = [c for c in options if len(neighbors[c]) == min_count]
            nxt = random.choice(candidates)
        else:
            # 4. Brak sasiadow -> losowe nieodwiedzone miasto
            remaining = [c for c in p1 if c not in visited]
            nxt = random.choice(remaining)

        child.append(nxt)
        visited.add(nxt)
        current = nxt

    return child


# --- APLIKACJA OKIENKOWA (GUI) ---


class TSPVisualizer(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Wizualizacja TSP: PMX, OX, CX, ERX & Brute Force (Dark Mode)")
        self.geometry("1080x760")
        self.minsize(900, 680)

        # Paleta kolorow - Dark Mode
        self.bg_main = "#121212"      # Glowne tlo (plotno)
        self.bg_panel = "#1e1e1e"     # Tlo panelu bocznego
        self.fg_text = "#e0e0e0"      # Jasnoszary tekst
        self.fg_muted = "#9e9e9e"     # Przygaszony tekst
        self.bg_input = "#2d2d2d"     # Tlo dla pol wprowadzania
        self.trough = "#3a3a3a"       # Tlo rowka suwakow
        self.accent = "#00e5ff"       # Kolor akcentu (najlepsza trasa)
        self.city_color = "#ff5252"   # Kolor miast

        self.configure(bg=self.bg_main)

        self.cities = []
        self.running = False
        self.best_path = None
        self.best_dist = float('inf')
        self.current_dist = float('inf')

        self.start_time = 0
        self.time_to_best = 0
        self.iterations = 0
        self.generator = None

        self.pop_size = 50
        self.mut_rate = 0.1

        self._init_styles()
        self.setup_ui()
        self.generate_cities()

    # --- Style ttk (clam respektuje kolory na macOS/Windows/Linux) ---

    def _init_styles(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        def button_style(name, bg, active, disabled):
            style.configure(name, background=bg, foreground="white",
                            font=("Arial", 11, "bold"), borderwidth=0,
                            focuscolor=bg, padding=6)
            style.map(name,
                      background=[("disabled", disabled), ("active", active)],
                      foreground=[("disabled", "#bdbdbd")])

        button_style("Start.TButton", "#2e7d32", "#1b5e20", "#1b3a1c")
        button_style("Stop.TButton", "#c62828", "#b71c1c", "#5a1f1f")
        button_style("Regen.TButton", "#37474f", "#455a64", "#263238")

        style.configure("Dark.TSpinbox", fieldbackground=self.bg_input,
                        foreground=self.fg_text, background=self.bg_panel,
                        arrowcolor=self.fg_text, bordercolor=self.trough,
                        lightcolor=self.trough, darkcolor=self.trough)
        style.map("Dark.TSpinbox", fieldbackground=[("readonly", self.bg_input)])

        style.configure("Dark.Horizontal.TScale", background=self.bg_panel,
                        troughcolor=self.trough, bordercolor=self.bg_panel,
                        lightcolor=self.accent, darkcolor=self.accent)

    # --- Pomocnicze budowanie UI ---

    def _make_section(self, parent, title):
        frame = tk.LabelFrame(parent, text=title, bg=self.bg_panel, fg=self.accent,
                              font=("Arial", 9, "bold"), padx=8, pady=6, bd=1,
                              relief="groove")
        frame.pack(fill=tk.X, pady=(0, 8))
        return frame

    def _slider_row(self, parent, label_text, scale_attr, val_attr, formatter):
        head = tk.Frame(parent, bg=self.bg_panel)
        head.pack(fill=tk.X)
        tk.Label(head, text=label_text, bg=self.bg_panel, fg=self.fg_text,
                 font=("Arial", 8)).pack(side=tk.LEFT)
        val_lbl = tk.Label(head, text="", bg=self.bg_panel, fg=self.accent,
                           font=("Arial", 8, "bold"))
        val_lbl.pack(side=tk.RIGHT)
        setattr(self, val_attr, val_lbl)

        def on_move(v):
            getattr(self, val_attr).config(text=formatter(float(v)))

        scale = ttk.Scale(parent, orient=tk.HORIZONTAL,
                          style="Dark.Horizontal.TScale", command=on_move)
        scale.pack(fill=tk.X, pady=(0, 4))
        setattr(self, scale_attr, scale)
        return scale

    def setup_ui(self):
        control_frame = tk.Frame(self, width=280, bg=self.bg_panel, padx=12, pady=10)
        control_frame.pack(side=tk.LEFT, fill=tk.Y)
        control_frame.pack_propagate(False)

        # Naglowek
        tk.Label(control_frame, text="TSP - Algorytmy Genetyczne",
                 bg=self.bg_panel, fg=self.fg_text,
                 font=("Arial", 12, "bold")).pack(anchor=tk.W, pady=(0, 2))
        tk.Label(control_frame, text="Problem komiwojazera",
                 bg=self.bg_panel, fg=self.fg_muted,
                 font=("Arial", 8)).pack(anchor=tk.W, pady=(0, 10))

        # --- Sekcja: Miasta ---
        sec_cities = self._make_section(control_frame, "Miasta")
        row = tk.Frame(sec_cities, bg=self.bg_panel)
        row.pack(fill=tk.X)
        tk.Label(row, text="Liczba:", bg=self.bg_panel, fg=self.fg_text,
                 font=("Arial", 9)).pack(side=tk.LEFT)
        self.points_var = tk.IntVar(value=10)
        self.spinbox = ttk.Spinbox(row, from_=3, to=100, width=6,
                                   textvariable=self.points_var,
                                   command=self.generate_cities,
                                   style="Dark.TSpinbox")
        self.spinbox.pack(side=tk.LEFT, padx=(6, 0))
        self.btn_regen = ttk.Button(sec_cities, text="Generuj nowe miasta",
                                    style="Regen.TButton", command=self.generate_cities)
        self.btn_regen.pack(fill=tk.X, pady=(8, 0))

        # --- Sekcja: Algorytm ---
        sec_algo = self._make_section(control_frame, "Algorytm")
        self.algo_var = tk.StringVar(value="ERX")
        algos = ["Brute Force", "GA - PMX", "GA - OX", "GA - CX", "GA - ERX"]
        for algo in algos:
            val = algo.split(" - ")[-1] if "GA" in algo else "BF"
            tk.Radiobutton(sec_algo, text=algo, variable=self.algo_var, value=val,
                           bg=self.bg_panel, fg=self.fg_text,
                           selectcolor=self.bg_input, activebackground=self.bg_panel,
                           activeforeground=self.accent, font=("Arial", 9),
                           command=self.on_algo_change).pack(anchor=tk.W)

        # --- Sekcja: Parametry GA ---
        sec_ga = self._make_section(control_frame, "Parametry GA")
        self._slider_row(sec_ga, "Rozmiar populacji", "scale_pop", "lbl_pop_val",
                         lambda v: str(int(round(v / 10) * 10)))
        self.scale_pop.configure(from_=10, to=200)
        self.scale_pop.set(50)
        self._slider_row(sec_ga, "Mutacja [%]", "scale_mut", "lbl_mut_val",
                         lambda v: str(int(round(v))))
        self.scale_mut.configure(from_=0, to=100)
        self.scale_mut.set(10)

        # --- Sekcja: Animacja ---
        sec_anim = self._make_section(control_frame, "Animacja")
        self._slider_row(sec_anim, "Szybkosc", "scale_speed", "lbl_speed_val",
                         lambda v: str(int(round(v))))
        self.scale_speed.configure(from_=1, to=100)
        self.scale_speed.set(90)

        # --- Przyciski START / STOP ---
        btn_row = tk.Frame(control_frame, bg=self.bg_panel)
        btn_row.pack(fill=tk.X, pady=(2, 8))
        self.btn_start = ttk.Button(btn_row, text="START", style="Start.TButton",
                                    command=self.start_algorithm)
        self.btn_start.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 4))
        self.btn_stop = ttk.Button(btn_row, text="STOP", style="Stop.TButton",
                                   command=self.stop_algorithm)
        self.btn_stop.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(4, 0))
        self.btn_stop["state"] = "disabled"

        # --- Statystyki ---
        stats_frame = self._make_section(control_frame, "Statystyki")
        self.lbl_status = tk.Label(stats_frame, text="Gotowy", bg=self.bg_panel,
                                   fg="#66bb6a", font=("Arial", 9, "bold"))
        self.lbl_status.pack(anchor=tk.W, pady=(0, 4))
        self.lbl_dist = tk.Label(stats_frame, text="Najkrotszy dystans: -",
                                 bg=self.bg_panel, fg=self.fg_text, font=("Arial", 9))
        self.lbl_dist.pack(anchor=tk.W)
        self.lbl_curr = tk.Label(stats_frame, text="Biezacy dystans: -",
                                 bg=self.bg_panel, fg=self.fg_muted, font=("Arial", 9))
        self.lbl_curr.pack(anchor=tk.W)
        self.lbl_iter = tk.Label(stats_frame, text="Iteracja/Generacja: 0",
                                 bg=self.bg_panel, fg=self.fg_text, font=("Arial", 9))
        self.lbl_iter.pack(anchor=tk.W)
        self.lbl_time_total = tk.Label(stats_frame, text="Czas trwania: 0.00s",
                                       bg=self.bg_panel, fg=self.fg_text, font=("Arial", 9))
        self.lbl_time_total.pack(anchor=tk.W)
        self.lbl_time_best = tk.Label(stats_frame, text="Znaleziono w czasie: 0.00s",
                                      bg=self.bg_panel, fg=self.fg_text, font=("Arial", 9))
        self.lbl_time_best.pack(anchor=tk.W)

        # --- Legenda ---
        legend = self._make_section(control_frame, "Legenda")
        self._legend_row(legend, self.accent, "Najlepsza trasa")
        self._legend_row(legend, "#777777", "Aktualnie sprawdzana")
        self._legend_row(legend, self.city_color, "Miasto")

        # Plotno
        self.canvas = tk.Canvas(self, bg=self.bg_main, highlightthickness=0)
        self.canvas.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        self.canvas.bind("<Configure>", lambda e: self.draw_cities())

    def _legend_row(self, parent, color, text):
        row = tk.Frame(parent, bg=self.bg_panel)
        row.pack(fill=tk.X, anchor=tk.W)
        swatch = tk.Canvas(row, width=18, height=12, bg=self.bg_panel,
                           highlightthickness=0)
        swatch.create_line(0, 6, 18, 6, fill=color, width=3)
        swatch.pack(side=tk.LEFT, padx=(0, 6))
        tk.Label(row, text=text, bg=self.bg_panel, fg=self.fg_text,
                 font=("Arial", 8)).pack(side=tk.LEFT)

    # --- Logika ---

    def on_algo_change(self):
        state = "normal" if self.algo_var.get() != "BF" else "disabled"
        self.scale_pop.configure(state=state)
        self.scale_mut.configure(state=state)

    def calculate_distance(self, path):
        dist = 0
        for i in range(len(path)):
            c1 = self.cities[path[i]]
            c2 = self.cities[path[(i + 1) % len(path)]]
            dist += math.hypot(c1[0] - c2[0], c1[1] - c2[1])
        return dist

    def generate_cities(self):
        self.stop_algorithm()
        num_cities = self.points_var.get()
        if self.algo_var.get() == "BF" and num_cities > 11:
            messagebox.showwarning("Uwaga!", "Brute Force dla wiecej niz 10-11 miast "
                                   "zajmie bardzo duzo czasu (zlozonosc O(n!)).")

        self.update_idletasks()
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()

        if width < 150:
            width = 700
        if height < 150:
            height = 700

        margin = 50

        self.cities = []
        for _ in range(num_cities):
            x = random.randint(margin, width - margin)
            y = random.randint(margin, height - margin)
            self.cities.append((x, y))

        self.best_path = None
        self.best_dist = float('inf')
        self.current_dist = float('inf')
        self.iterations = 0
        self.start_time = 0
        self.time_to_best = 0
        self.draw_cities()
        self.update_stats()

    def draw_cities(self, current_path=None):
        self.canvas.delete("all")

        if current_path and current_path != self.best_path:
            for i in range(len(current_path)):
                x1, y1 = self.cities[current_path[i]]
                x2, y2 = self.cities[current_path[(i + 1) % len(current_path)]]
                self.canvas.create_line(x1, y1, x2, y2, fill="#777777",
                                        width=1, dash=(2, 2))

        if self.best_path:
            for i in range(len(self.best_path)):
                x1, y1 = self.cities[self.best_path[i]]
                x2, y2 = self.cities[self.best_path[(i + 1) % len(self.best_path)]]
                self.canvas.create_line(x1, y1, x2, y2, fill=self.accent, width=3)

        for i, (x, y) in enumerate(self.cities):
            self.canvas.create_oval(x-6, y-6, x+6, y+6, fill=self.city_color,
                                    outline=self.bg_main, width=2)
            self.canvas.create_text(x, y-15, text=str(i), fill=self.fg_text,
                                    font=("Arial", 10, "bold"))

    def set_status(self, text, color):
        self.lbl_status.config(text=text, fg=color)

    def update_stats(self):
        self.lbl_dist.config(
            text=f"Najkrotszy dystans: {self.best_dist:.2f}"
            if self.best_dist != float('inf') else "Najkrotszy dystans: -")
        self.lbl_curr.config(
            text=f"Biezacy dystans: {self.current_dist:.2f}"
            if self.current_dist != float('inf') else "Biezacy dystans: -")
        self.lbl_iter.config(text=f"Iteracja/Generacja: {self.iterations}")

        if self.running:
            total = time.time() - self.start_time
        elif self.start_time != 0:
            total = self.time_to_best
        else:
            total = 0.0
        self.lbl_time_total.config(text=f"Czas trwania: {total:.2f}s")
        self.lbl_time_best.config(text=f"Znaleziono w czasie: {self.time_to_best:.2f}s")

    def brute_force_generator(self):
        base_path = list(range(len(self.cities)))
        for path in itertools.permutations(base_path):
            if not self.running:
                break
            self.iterations += 1
            dist = self.calculate_distance(path)
            self.current_dist = dist

            is_new_best = False
            if dist < self.best_dist:
                self.best_dist = dist
                self.best_path = path
                self.time_to_best = time.time() - self.start_time
                is_new_best = True

            yield path, is_new_best

    def ga_generator(self, crossover_func):
        pop_size = self.pop_size
        num_cities = len(self.cities)

        population = [list(range(num_cities)) for _ in range(pop_size)]
        for p in population:
            random.shuffle(p)

        while self.running:
            self.iterations += 1
            fitness = [(path, self.calculate_distance(path)) for path in population]
            fitness.sort(key=lambda x: x[1])

            current_best_path, current_best_dist = fitness[0]
            self.current_dist = current_best_dist
            is_new_best = False

            if current_best_dist < self.best_dist:
                self.best_dist = current_best_dist
                self.best_path = current_best_path
                self.time_to_best = time.time() - self.start_time
                is_new_best = True

            new_population = [fitness[0][0], fitness[1][0]]

            while len(new_population) < pop_size:
                p1 = min(random.sample(fitness, 3), key=lambda x: x[1])[0]
                p2 = min(random.sample(fitness, 3), key=lambda x: x[1])[0]

                child = crossover_func(p1, p2)

                if random.random() < self.mut_rate:
                    idx1, idx2 = random.sample(range(num_cities), 2)
                    child[idx1], child[idx2] = child[idx2], child[idx1]

                new_population.append(child)

            population = new_population
            yield current_best_path, is_new_best

    def start_algorithm(self):
        if len(self.cities) < 3:
            return
        self.running = True
        self.btn_start["state"] = "disabled"
        self.btn_stop["state"] = "normal"
        self.spinbox.configure(state="disabled")
        self.btn_regen.configure(state="disabled")

        # Zamrozenie parametrow na czas dzialania
        self.pop_size = int(round(self.scale_pop.get() / 10) * 10)
        self.mut_rate = round(self.scale_mut.get()) / 100.0

        self.start_time = time.time()
        self.time_to_best = 0
        self.iterations = 0
        self.best_dist = float('inf')
        self.best_path = None
        self.current_dist = float('inf')

        algo = self.algo_var.get()
        algo_names = {"BF": "Brute Force", "PMX": "GA-PMX", "OX": "GA-OX",
                      "CX": "GA-CX", "ERX": "GA-ERX"}
        self.set_status(f"Dziala: {algo_names.get(algo, algo)}", self.accent)

        if algo == "BF":
            self.generator = self.brute_force_generator()
        elif algo == "PMX":
            self.generator = self.ga_generator(pmx)
        elif algo == "OX":
            self.generator = self.ga_generator(ox)
        elif algo == "CX":
            self.generator = self.ga_generator(cx)
        elif algo == "ERX":
            self.generator = self.ga_generator(erx)

        self.run_step()

    def stop_algorithm(self):
        was_running = self.running
        self.running = False
        self.btn_start["state"] = "normal"
        self.btn_stop["state"] = "disabled"
        self.spinbox.configure(state="normal")
        self.btn_regen.configure(state="normal")
        if hasattr(self, "lbl_status") and was_running:
            self.set_status("Zatrzymano", "#ffb74d")
        if hasattr(self, "start_time") and self.start_time != 0:
            self.update_stats()

    def run_step(self):
        if not self.running:
            return

        try:
            steps_per_frame = 1 if self.algo_var.get() != "BF" else 1000

            current_path = self.best_path
            for _ in range(steps_per_frame):
                current_path, is_new_best = next(self.generator)
                if is_new_best:
                    break

            self.draw_cities(current_path)
            self.update_stats()

            delay = max(1, 101 - int(round(self.scale_speed.get())))
            self.after(delay, self.run_step)

        except StopIteration:
            self.running = False
            self.stop_algorithm()
            self.set_status("Zakonczono", "#66bb6a")
            self.draw_cities()
            messagebox.showinfo("Koniec", "Przeszukano cala przestrzen!")


if __name__ == "__main__":
    app = TSPVisualizer()
    app.mainloop()
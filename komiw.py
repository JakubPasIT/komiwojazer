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

# --- APLIKACJA OKIENKOWA (GUI) ---

class TSPVisualizer(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Wizualizacja TSP: PMX, OX, CX & Brute Force (Dark Mode)")
        self.geometry("1000x700")

        # Paleta kolorów - Dark Mode
        self.bg_main = "#121212"      # Główne tło (płótno)
        self.bg_panel = "#1e1e1e"     # Tło panelu bocznego
        self.fg_text = "#e0e0e0"      # Jasnoszary tekst
        self.bg_input = "#2d2d2d"     # Tło dla pól wprowadzania

        self.configure(bg=self.bg_main)

        self.cities = []
        self.running = False
        self.best_path = None
        self.best_dist = float('inf')

        self.start_time = 0
        self.time_to_best = 0
        self.iterations = 0
        self.generator = None

        self.setup_ui()
        self.generate_cities()

    def setup_ui(self):
        # Panel boczny
        control_frame = tk.Frame(self, width=250, bg=self.bg_panel, padx=10, pady=10)
        control_frame.pack(side=tk.LEFT, fill=tk.Y)

        # Ustawienia
        tk.Label(control_frame, text="Liczba miast:", bg=self.bg_panel, fg=self.fg_text, font=("Arial", 10, "bold")).pack(anchor=tk.W, pady=(10, 0))
        self.points_var = tk.IntVar(value=10)

        # Spinbox w trybie ciemnym
        self.spinbox = tk.Spinbox(control_frame, from_=3, to=100, textvariable=self.points_var, command=self.generate_cities,
                                  bg=self.bg_input, fg=self.fg_text, insertbackground=self.fg_text, buttonbackground=self.bg_panel)
        self.spinbox.pack(fill=tk.X, pady=5)

        tk.Label(control_frame, text="Algorytm:", bg=self.bg_panel, fg=self.fg_text, font=("Arial", 10, "bold")).pack(anchor=tk.W, pady=(10, 0))
        self.algo_var = tk.StringVar(value="OX")
        algos = ["Brute Force", "GA - PMX", "GA - OX", "GA - CX"]
        for algo in algos:
            tk.Radiobutton(control_frame, text=algo, variable=self.algo_var, value=algo.split(" - ")[-1] if "GA" in algo else "BF",
                           bg=self.bg_panel, fg=self.fg_text, selectcolor=self.bg_input, activebackground=self.bg_panel, activeforeground="white").pack(anchor=tk.W)

        # Przyciski
        self.btn_start = tk.Button(control_frame, text="START", bg="#2e7d32", fg="white", activebackground="#1b5e20", activeforeground="white", font=("Arial", 12, "bold"), command=self.start_algorithm)
        self.btn_start.pack(fill=tk.X, pady=20)

        self.btn_stop = tk.Button(control_frame, text="STOP", bg="#c62828", fg="white", activebackground="#b71c1c", activeforeground="white", font=("Arial", 12, "bold"), command=self.stop_algorithm)
        self.btn_stop.pack(fill=tk.X)
        self.btn_stop["state"] = "disabled"

        # Statystyki
        stats_frame = tk.LabelFrame(control_frame, text="Statystyki", bg=self.bg_panel, fg=self.fg_text, padx=5, pady=5)
        stats_frame.pack(fill=tk.X, pady=20)

        self.lbl_dist = tk.Label(stats_frame, text="Najkrótszy dystans: -", bg=self.bg_panel, fg=self.fg_text)
        self.lbl_dist.pack(anchor=tk.W)

        self.lbl_iter = tk.Label(stats_frame, text="Iteracja/Generacja: 0", bg=self.bg_panel, fg=self.fg_text)
        self.lbl_iter.pack(anchor=tk.W)

        self.lbl_time_total = tk.Label(stats_frame, text="Czas trwania: 0.00s", bg=self.bg_panel, fg=self.fg_text)
        self.lbl_time_total.pack(anchor=tk.W)

        self.lbl_time_best = tk.Label(stats_frame, text="Znaleziono w czasie: 0.00s", bg=self.bg_panel, fg=self.fg_text)
        self.lbl_time_best.pack(anchor=tk.W)

        # Płótno
        self.canvas = tk.Canvas(self, bg=self.bg_main, highlightthickness=0)
        self.canvas.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        self.canvas.bind("<Configure>", lambda e: self.draw_cities())

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
            messagebox.showwarning("Uwaga!", "Brute Force dla więcej niż 10-11 miast zajmie bardzo dużo czasu (złożoność O(n!)).")

        # Odświeżamy widok, by pobrać aktualne wymiary
        self.update_idletasks()
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()

        # Zabezpieczenie przed niewyrenderowanym okienkiem (lub zbyt małym)
        if width < 150: width = 700
        if height < 150: height = 700

        margin = 50

        self.cities = []
        for _ in range(num_cities):
            x = random.randint(margin, width - margin)
            y = random.randint(margin, height - margin)
            self.cities.append((x, y))

        self.best_path = None
        self.best_dist = float('inf')
        self.draw_cities()
        self.update_stats()

    def draw_cities(self, current_path=None):
        self.canvas.delete("all")

        # Rysowanie najlepszej trasy (jasnoniebieska/cyjanowa gruba linia)
        if self.best_path:
            for i in range(len(self.best_path)):
                x1, y1 = self.cities[self.best_path[i]]
                x2, y2 = self.cities[self.best_path[(i + 1) % len(self.best_path)]]
                self.canvas.create_line(x1, y1, x2, y2, fill="#00e5ff", width=3)

        # Rysowanie aktualnie sprawdzanej trasy (ciemnoszara cienka linia)
        if current_path and current_path != self.best_path:
            for i in range(len(current_path)):
                x1, y1 = self.cities[current_path[i]]
                x2, y2 = self.cities[current_path[(i + 1) % len(current_path)]]
                self.canvas.create_line(x1, y1, x2, y2, fill="#555555", width=1, dash=(2, 2))

        # Rysowanie miast (neonowa czerwień)
        for i, (x, y) in enumerate(self.cities):
            self.canvas.create_oval(x-6, y-6, x+6, y+6, fill="#ff5252", outline=self.bg_main, width=2)
            self.canvas.create_text(x, y-15, text=str(i), fill=self.fg_text, font=("Arial", 10, "bold"))

    def update_stats(self):
        self.lbl_dist.config(text=f"Najkrótszy dystans: {self.best_dist:.2f}" if self.best_dist != float('inf') else "Najkrótszy dystans: -")
        self.lbl_iter.config(text=f"Iteracja/Generacja: {self.iterations}")
        self.lbl_time_total.config(text=f"Czas trwania: {time.time() - self.start_time:.2f}s" if self.running else f"Czas trwania: {self.time_to_best:.2f}s" if not self.start_time == 0 else "Czas trwania: 0.00s")
        self.lbl_time_best.config(text=f"Znaleziono w czasie: {self.time_to_best:.2f}s")

    def brute_force_generator(self):
        base_path = list(range(len(self.cities)))
        for path in itertools.permutations(base_path):
            if not self.running: break
            self.iterations += 1
            dist = self.calculate_distance(path)

            is_new_best = False
            if dist < self.best_dist:
                self.best_dist = dist
                self.best_path = path
                self.time_to_best = time.time() - self.start_time
                is_new_best = True

            yield path, is_new_best

    def ga_generator(self, crossover_func):
        pop_size = 50
        num_cities = len(self.cities)

        # Inicjalizacja populacji
        population = [list(range(num_cities)) for _ in range(pop_size)]
        for p in population:
            random.shuffle(p)

        while self.running:
            self.iterations += 1
            # Ocena (fitness)
            fitness = [(path, self.calculate_distance(path)) for path in population]
            fitness.sort(key=lambda x: x[1])

            current_best_path, current_best_dist = fitness[0]
            is_new_best = False

            if current_best_dist < self.best_dist:
                self.best_dist = current_best_dist
                self.best_path = current_best_path
                self.time_to_best = time.time() - self.start_time
                is_new_best = True

            # Selekcja i tworzenie nowej populacji (Elitaryzm)
            new_population = [fitness[0][0], fitness[1][0]]

            while len(new_population) < pop_size:
                # Turniejowa selekcja
                p1 = min(random.sample(fitness, 3), key=lambda x: x[1])[0]
                p2 = min(random.sample(fitness, 3), key=lambda x: x[1])[0]

                child = crossover_func(p1, p2)

                # Mutacja (Swap)
                if random.random() < 0.1:
                    idx1, idx2 = random.sample(range(num_cities), 2)
                    child[idx1], child[idx2] = child[idx2], child[idx1]

                new_population.append(child)

            population = new_population
            yield current_best_path, is_new_best

    def start_algorithm(self):
        if len(self.cities) < 3: return
        self.running = True
        self.btn_start["state"] = "disabled"
        self.btn_stop["state"] = "normal"
        self.spinbox.configure(state="disabled") # Blokada edycji miast

        self.start_time = time.time()
        self.time_to_best = 0
        self.iterations = 0
        self.best_dist = float('inf')
        self.best_path = None

        algo = self.algo_var.get()
        if algo == "BF":
            self.generator = self.brute_force_generator()
        elif algo == "PMX":
            self.generator = self.ga_generator(pmx)
        elif algo == "OX":
            self.generator = self.ga_generator(ox)
        elif algo == "CX":
            self.generator = self.ga_generator(cx)

        self.run_step()

    def stop_algorithm(self):
        self.running = False
        self.btn_start["state"] = "normal"
        self.btn_stop["state"] = "disabled"
        self.spinbox.configure(state="normal") # Odblokowanie edycji miast
        if hasattr(self, 'start_time') and self.start_time != 0:
             self.update_stats()

    def run_step(self):
        if not self.running: return

        try:
            # Aby UI nie zacięło się, wykonujemy kilka iteracji przed odświeżeniem ekranu
            steps_per_frame = 1 if self.algo_var.get() != "BF" else 1000

            for _ in range(steps_per_frame):
                current_path, is_new_best = next(self.generator)
                if is_new_best:
                    break # Przerwij pętlę wczesniej żeby od razu narysować nową trasę

            self.draw_cities(current_path)
            self.update_stats()

            # Zapętlamy używając after (asynchroniczność w Tkinter)
            self.after(10, self.run_step)

        except StopIteration:
            self.stop_algorithm()
            self.draw_cities()
            messagebox.showinfo("Koniec", "Przeszukano całą przestrzeń!")

if __name__ == "__main__":
    app = TSPVisualizer()
    app.mainloop()
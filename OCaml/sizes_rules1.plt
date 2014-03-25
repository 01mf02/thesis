# adapted from proof_sizes.plt

i = 1

directory = "sizes/"

set terminal tikz size 6cm,6cm
set output directory."sizes_rules".i.".tex"

# show legend above the plot
set key above

set xlabel "Variables"
set xrange [0:30]
set xtics 5

if (i == 1) { rules_max = 50000; symbs_max = 700000 }

# filenames
file_b = directory."sizes_b".i.".dat"
file_d = directory."sizes_d".i.".dat"

# show numbers like "500k", "5G", ...
set format y "%.0s%c"

set style data linespoints
set style line 1 pi -1 pt 6
set style line 2 pi -1 pt 1

b(x) = b1 + b2*x**2 + b3*b4**x
d(x) = d1 + d2*x + d3*x**2 + d4*x**3

n = 2

set origin 0,0
set ylabel "Rules"
set yrange [0:rules_max]

fit b(x) file_b using 1:n via b1, b2, b3, b4
fit d(x) file_d using 1:n via d1, d2, d3, d4

plot file_b using 1:n ls 1 title 'Base', \
	 file_d using 1:n ls 2 title 'Dec.', \
	 b(x) title 'BF', \
	 d(x) title 'DF'

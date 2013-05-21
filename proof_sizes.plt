# i denotes the index of the data file for the current plot
# i will be set from calling batch.plt; uncomment line below if you want to
# run this plot file without batch.plt
#i = 5

#set terminal pdf
#set output "proof_sizes".i.".pdf"
set terminal tikz size 12cm,6cm
set output "proof_sizes".i.".tex"

# show legend above the plot
set key above

set xlabel "Variables"
set xrange [0:30]
set xtics 5

# different axes for different data sets
if (i == 0) { rules_max =  5000; symbs_max = 100000 }
if (i == 1) { rules_max = 50000; symbs_max = 700000 }
if (i == 2) { rules_max =  5000; symbs_max = 200000 }
if (i == 3) { rules_max = 50000; symbs_max = 500000 }
if (i == 4) { rules_max = 50000; symbs_max = 500000 }
if (i == 5) { rules_max = 50000; symbs_max = 500000 }

# filenames
file_b = "sizes_b".i.".dat"
file_d = "sizes_d".i.".dat"

# show numbers like "500k", "5G", ...
set format y "%.0s%c"

set style data linespoints
set style line 1 pi -1 pt 6
set style line 2 pi -1 pt 1

# for debugging, output all line styles
#show style line

set size square 1,0.5
set multiplot layout 1,2

# polynomials to approximate base/decomposition curves
b(x) = b1 + b2*x + b3*x**2 + b4*x**3
d(x) = d1 + d2*x + d3*x**2 + d4*x**3

# exponential function to approximate base curve in special cases
if (i == 1 || i == 3 || i == 4 || i == 5) { b(x) = b1 + b2*x**2 + b3*b4**x }
if (                    i == 4 || i == 5) { d(x) = d1 + d2*x**2 + d3*d4**x }

# n denotes the column number in the data file
# (n = 2 -> rules, n = 3 -> symbols)
do for [n = 2:3] {
	if (n == 2) {
		set origin 0,0
		set ylabel "Rules"
		set yrange [0:rules_max]
	}
	if (n == 3) {
		set origin 0.5,0
		set ylabel "Symbols"
		set yrange [0:symbs_max]
	}

	fit b(x) file_b using 1:n via b1, b2, b3, b4
	fit d(x) file_d using 1:n via d1, d2, d3, d4

	plot file_b using 1:n ls 1 title 'Base', \
	     file_d using 1:n ls 2 title 'Dec.', \
	     b(x) title 'BF', \
	     d(x) title 'DF'
	
	# reset the coefficients from the fitting functions
	# in case we do not do that, the fitting process may go awry!
	undefine b* d*
}

set nomultiplot


# don't quit terminal immediately after drawing (for X11 output)
#pause -1

set output
set terminal pop

# Generate plots with GNU plot.
# Most of it is generated with ChatGPT.

# Variables
CSV_FILES = n6t1f0_inductive.csv n6t1f1_inductive.csv n6t1f1-agreement-sim20.csv
OUTPUT_PNGS = $(CSV_FILES:.csv=.png)
GNUPLOT_SCRIPT = cactus.plt

# Default target
all: $(OUTPUT_PNGS)

# Rule to generate each PNG file from its corresponding CSV file
%.png: %.csv $(GNUPLOT_SCRIPT)
	gnuplot -e "input_name='$<'" -e "output_name='$@'" $(GNUPLOT_SCRIPT)

# Clean target to remove the generated PNG files
clean:
	rm -f $(OUTPUT_PNGS)

# Phony targets
.PHONY: all clean

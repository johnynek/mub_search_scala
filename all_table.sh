#!/bin/sh
for dim in 2 3 4 5 6
do
  #for root in 2 3 4 6 8 9 10 12 15 16 18 20 24 27 32
  for root in 24 36
  do
    echo "dim = $dim, root = $root"
    time ./mubs write_table --dim $dim --root $root --orth --quant1 --output "tabs/orth_dim=${dim}_root=${root}_quant1"
    time ./mubs write_table --dim $dim --root $root --unbiased --quant1 --output "tabs/unbiased_dim=${dim}_root=${root}_quant1"
  done
done

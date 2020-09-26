#!/bin/sh
for dim in 2 3 4 5 6
do
  #for root in 2 3 4 6 8 9 10 12 15 16 18 20 24 27 32
  for root in 36
  do
    echo "dim = $dim, root = $root"
    time ./mubs write_table --dim $dim --root $root --orth --output "tabs/orth_dim=${dim}_root=${root}"
    time ./mubs write_table --dim $dim --root $root --unbiased --output "tabs/unbiased_dim=${dim}_root=${root}"
  done
done

First install CMU's BAP tool:

    opam init --comp=4.05.0  
    eval `opam config env`
    opam depext --install bap
  
  Note: bap requires your ocaml version to be between 4.03 and 4.06 (not including 4.06)

To run the python script, just give it the name of a MIPS binary. You can use the GCC cross compiler to create a MIPS binary.

This will create a file called cfi.v in ../src

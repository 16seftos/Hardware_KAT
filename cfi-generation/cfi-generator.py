#!/usr/bin/env python3

import sys
import subprocess

def main(binary):
  # Initialize arrays
  build_node = []
  nodes = []
  nodeinfo = []

  # Run bap on the provided binary, and remove the first 5 lines
  lines = subprocess.getoutput("bap " + binary + " -d --print-symbol=main")
  lines = lines.split('\n')
  lines = lines[5:]

  for line in lines:
    # Clean up lines so they are readable
    line = line.strip('\n')
    # If the line is empty (no instruction) then a node has ended
    # If a node has been built, add it to the list of nodes
    if not line and build_node:
      nodes.append(build_node)
      build_node = []
    # If the line has an instruction then add it to the current node
    elif line:
      build_node.append(line)

  # Extract the memory addresses for each node, node entrance, and node exit
  counter = 0
  for node in nodes:
    exits = []

    # Node names initially exist in the form of 'xxxxxxxx: ' where 'x' is a hex value
    name = "node" + str(counter)

    # Separate the instruction from the address of the entrance, and store only the entrance
    entrance = node[0]
    entrance = entrance.split()[0]
    entrance = entrance[:-1]

    # Iterate through every instruction in the node and extract the address for any line that contains a jump or branch
    for instr in node:
      if 'goto' in instr or 'call' in instr or 'return' in instr:
        if 'RA' in instr:
          exit = (instr.split()[0][:-1], instr.split()[-1])
        else:
          exit = (instr.split()[0][:-1], instr.split()[-1][1:])
        exits.append(exit)

    # Add the node name, entrance, and list of exits to a list of all nodes
    nodeinfo.append([name, entrance, exits])
    counter += 1

  build_cfi(nodeinfo)

# This function generates cfi.v based on the information from bap
def build_cfi(node_components):
  nodes = []

# This string contains all the necessary imports, and the header for the CFI section.
  cfi_header = """Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith ZArith.
Require Import Vector. 
Require Import String.
Require Import JMeq.
Require Import List. Import ListNotations.

Require Import Integers.

Require Import lang.
Require Import combinators.


Section CFI.
  Variables i o : id TVec64.

  Definition lowerbits := Int64.repr 4095.
  Definition upperbits := Int64.repr 16773120.\n\n"""

  f = open('../src/cfi.v', 'w')
  f.write(cfi_header)

  # Builds a list of the nodes, to be stored as an integer by cfi.v
  for node in node_components:
    node_end = node[-1][-1][0]
    node_start = node[1]
    node_end = str(int(node_end, 16))
    node_start = str(int(node_start, 16))
    nodes.append((node[0], node_start + node_end))

  # Writes the list of nodes to cfi.v
  for node in nodes:
    f.write("  Definition " + node[0] + " := Int64.repr " + node[1] + ".\n")

  # MISSING
  # When the current instruction is a jump, determine if the jump is allowed by the CFG

  f.write("End CFI.\n")
  f.close()

def usage():
  print("Usage:\n" + str(sys.argv[0]) + " <Mips Binary>")


if __name__ == "__main__":
  if len(sys.argv) != 2:
    usage()
  else:
    main(sys.argv[1])

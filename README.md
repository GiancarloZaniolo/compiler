#### Authorship
  * Authors: 
    * Elan Biswas (<elanb@andrew.cmu.edu>)
    * Giancarlo Zaniolo (<gzaniolo@andrew.cmu.edu>)
 * L1 Starter Code:
    * Author: Frank Pfenning (<fp@cs.cmu.edu>)
    * Modified: Anand Subramanian (<asubrama@andrew.cmu.edu>)
    * Modified for OCaml from SML: Michael Duggan (<md5i@cs.cmu.edu>)
    * Modified: Alice Rao (<alrao@andrew.cmu.edu>)
    * Modified: Nick Roberts (<nroberts@alumni.cmu.edu>)
    * Modified: Henry Nelson (<hcnelson99@gmail.com>)

---

### Notes to build and run compiler:
In order to build the compiler, you must first install the correct versions of all of the necessary dependancies. 
All dependancies can be found in the cmu411/autograder-ocaml docker image.

To create an instance of the docker container, download docker, and run:\
`docker pull cmu411/autograder-ocaml:latest`\
`docker run --name 411 -td cmu411/autograder-ocaml:latest`\
`docker exec -it 411 bash`\
Next, clone this repository in the docker container, and type `make` while in the main directory to build it.

The compiler executable will is located at `./bin/c0c`

Importantly, the compiler supports compilation to different target architectures including abs (abstract three-address assembly), x86-64, arm64, and llvm (LLVM IR). It also supports optimizations `-O0` through `-O3`, though `-O2` and `-O3` are only available for x86-64  and arm64 targets, as they involve leveraging llvm.\
If you wish to link external functions to enable functionality not available in the l4 language (a subset of c0), such as printing, or floating-point arithmetic, you can attach a header file with function prototypes using `-l example_proto.h`

Information on the available compiler flags can be found by running `./bin/c0c --help`

Additionally, a few example files are available in `./examples` for you to try out.\
On an x86-64 machine, you would run `./bin/c0c -e x86-64 ./examples/FILE` to generate the object file, and then link it to a bench that will run it using `gcc`. A simple bench is provided at `./examples/bench.c`.

The rest of this document contains design decisions taken during the creation of the compiler, and at the very bottom, an explanation of what each file does.

---

## Lab 6 Project
For Lab 6, we added LLVM backend support. As an extension, we used the ability of the compiler to target the LLVM IR to implement an ARM64 backend as well as two new optimization levels.

## Usage
To compile a file to x86-64 assembly, use the execute `bin/c0c -ex86-64 <filename>` from the compiler root directory. Optimization level can be specified with `-On` where `n` specifies the level, which can range from 0 to 3. Other targets include LLVM (with the `-ellvm` flag) and ARM64 (with the `-earm64` flag). 

## Code Layout

 This is an optimizing compiler for the L4 language, a subset of the C0 language that supports function calls, loops, conditionals, and memory operations. The compiler pipeline consists of lexing, parsing, an elaboration step, IR-tree translation, three-address code-generation, optimization, register allocation, and a final two-address code-generator—which is then formatted directly as x86-64 assembly.

---
## Important Design Decisions

### Parsing
Parsing allows us to construct a syntax tree according to the L4 grammar, greatly simplifying the translation operations done in future steps. We accomplish this using a modified version of the L1 starter parser, which itself is generated via Menhir. Design decision regarding the parsing of the L4 grammar extensions include:
  * `for` loops are allowed to parse with non-\<simp\> statements in the first and third components. This makes it easier for the compiler to preserve source span information for the generation of helpful error messages when we do semantic analysis.  
  * To avoid the ambiguity caused by the pointer/multiplication operator conflict, type identifiers are lexed into a different token than other identifiers. This puts the burden of disambiguation on the lexer, which now has to maintain state to determine which token to emit for identifiers, but this neatly simplifies the disambiguation for the parser.

### Elaboration
As discussed in lecture, we elaborate the parsed abstract syntax tree into a form more amenable to future passes over the program. The elaboration consists of a number of simplifications of the L4 language structure, such as the translation of `for` loops into `while` loops and the translation of logical boolean operators into ternary expressions. This simplifies the logic of both typechecking and the following IR translation step. Having this step be separate from the initial parsing step also made it easier to debug as it simplifiies the parser code and isolates the structural changes into their own module.

As a consequence of converting `for` loops into `while` loops, we must check in the elaboration step that the first and third components of the `for` loop are simps. We must also check during elaboration that the third component is not a declaration. This is because the type checker has no way of knowing that the translated `while` loop was once a `for` loop. 

Other translations include elaboating (`~x`) to (`(-1) ^ x`) and (`-x`) to (`0 - x`). We also elaborate the logical operators `&&` and `||` into the ternary operator as suggested in the lab handout. Similar to the aforementioned `for` loop case, these serve to simplify future case work.

We do not elaborate compound assignments to \<dest\> = \<dest\> \<op\> \<int\> as lvalues can be effectful.
### Type Checking
We perform type checking in a single pass by extending the environment of the L1 starter code environment to track information about variable delcarations/initializations, function declarations/definitions, type definitions, and struct definitions. Passing these declared and initialized sets as inputs into and returning them as outputs from recursive type checking calls allows us to easily and efficiently implement the initialization, returrn, and type checking judgement rules from lecture in a single pass. Specifically, we defined the environment as a record of sets and a boolean:
  * A declared/initialized set that maps previously *declared* and *defined* variables to their types
  * A function declaration context that tracks which functions have been declared, defined, and called throughout the program.
  * A type-definition context that maps type-defined identifiers to their fully-resolved type.
  * A struct-definition context that maps struct names to a mapping of fields to types.
  * A boolean `returns` that indicates that the program returns on this control flow path.
  * A return-type field which tracks the return type of the current function

This record is sufficient for computing all of the necessary semantic analyses in a single pass. We typecheck after the elaboration step as the simplifications to the program structure reduces the necessary case work. One drawback of this method is that we must preserve the mark information generated by the parser in the elaboration step if we want to produce useful compiler error messages. As we modify the program structure, some constructs in the elaborated AST do not correspond to lines or characters in the original code, so the mark information may not be totally accurate. 

After extending our compiler to support L4, it became necessary to track the types of subexpressions so that code generation can utilize correctly-sized registers and instructions. As we compute typing information during typechecking, we decided to reuse this information by turned typechecking into a translation step that annotates each expression in the AST. To reuse code and for ease of implementing, we simply extended the elaborated AST to include type annotations on each expression. Since the elaboration step must produce this tree without typing information, it produces dummy types that are filled in by the type checker. In the future it may be prudent to create a new typed-AST that is separate from the tree generated after elaboration.

Two of the data structures--the function declaration context and the typedef context--that we compute during typechecking contain information that is also useful during the first IR translation step. To reuse these, we return them from the typechecker in addition to the translated AST.

### IR Tree Generation
The elaborated syntax tree was translated by recursively traversing through its statements and expressions, and constructing the equivalent IR tree expressions, notably separating impure expressions and boolean expressions in conditionals from pure expressions. Temps were created wherever necessary. The IR Tree datatype was created to closely resemble what was given in the lecture notes, along with a few
key design decisions:
  * While loops were made with a single loop guard at the top, and an unconditional jump back to the loop guard at the bottom
  * Any if statements had explicit labels and jumps for each case, instead of falling through to the first case when fulfilling the conditional jump condition in order to ensure the program is composed of well-formed basic blocks.
  * Boolean expressions in conditionals were implemented as shown in the lecture notes, always evaluating to conditional binop
  * Normally, typechecking forces variable declarations to shadow function names. However, if a function is used
  in the same line as the variable with its name is declared, this is allowed. This edge case was circumvented by
  elaborating the program through inserting temps to make the expression come before the variable declaration. 
  This case is de-elaborated in the IR "Declare" case for statements
  * Types are fully elaborated in IR, meaning that every temp is sized, and every array access or struct field access is assigned a specific number or temp as an offset 
  * Struct definitions no longer exist in IR
  * The IR tree structure contains all functionality such that dynamic semantics, such as null and offset checks
  are not explicitly elaborated
  
### Quad Tree Generation
The Quad Tree datatype was created to initially perform optimizations on, and afterwards to clearly convey register useage information to the register allocator. The initial transformation was done by iterating through IR tree commands and expanding the necessary details, such as pure expressions, and leaving in things like labels and `if` statements. Pure expressions are decoded using a maximal munch algorithm. Impure expressions were individually cased on and manually expanded to produce correct code. The initial translation delays all use of registers so that all optimization passes have and less to case on. This is especially the case because our compiler does SSA optimizations, and predefined registers interrupt SSA, as a register will likely be assigned to multiple times.

All of the dynamic semantics for memory operations are elaborated in the initial quad tree generation. This 
includes null checks, array bounds checking, alloc_array size checking, and other such operations. However, memory
reads and writes get their own separate instruction, they are not a part of the general "Move" instruction. Also, array accesses with elements of size 4 or 8 are changed to LEAQ.

### Analysis Passes
## Control Flow Graph
The control flow graph is represented as a graph of nodes, with edges representing control flow. Each node is represented by a label, and both forward and reverse control flow edges are present in the graph. In addition to the graph skeleton, each label is mapped to some data related to its corresponding basic block. This data was made polymorphic so that data computed for each basic block could be easily stored in the CFG itself. This was implemented by making the CFG a thin layer over the OCaml Core Hash_tbl library and our previously-implemented graph library.

## Dataflow Analysis
We implemented a dataflow framework inspired by the Dragon Book. It allows for the efficient computation of the maximum fixed point of a set of dataflow equations. The user of the framework is required to define the dataflow problem by providing a definition of the meet semi-lattice, the dataflow equations, some initial values, and the CFG to compute the dataflow on. The framework then provides a mapping in the form of a CFG with the fixed-point solutions. This framework was used extensively for computing temporary register liveness information and partial redundancy elimination.

## Dominator Tree
The implementation of SSA translation and ADCE make use of the dominance relation. Our implementation follows "A simple, fast dominance algorithm", which produces a 
"reverse" dominator tree. (i.e. A tree where every node points to its immediate dominator.) As such, the library also exposes a reversal function that takes the transpose of the tree to the traditional dominator tree representation, as both are useful.

## Dominance Frontier Tree
The implemenation given by "A simple, fast dominance algorithm" yields a simple way to compute the dominance frontier of each node in the CFG using a two-finger traversal algorithm. This is used for SSA translation and ADCE.

## Basic Purity Analysis
We implemented a very basic form of purity analysis, where the compiler iterates through all of the statements in a control flow graph (a function), and returns false if it contains any statements that could potentially be impure. Our purity analysis assumes that all function calls are impure. Although it is possible to calculate the purity of function calls using a call graph, we did not have time to implement it. Purity analysis is an analysis pass which we use in ADCE, and could be used to improve PRE, but we did not have time to implement it during this assignment.

## Static Single Assignment
Our method for Static Single-Assignment (SSA) construction was based off the basic algorithm presented in "SSA-Based Compiler Design". Our implementation uses phi functions as an instruction. Our destruction uses a notion of "parallel copy" blocks so that extra basic blocks are only created if they are necessary.

### Optimizations
The following sections describe the optimizations in the order that they (first) appear in the compiler.

## Non-SSA Based Local Copy Propagation
This is a simple pass that propagates constants and variables through a basic block. It does not assume SSA form and is used primarily to make partially redundant expressions more visible to the PRE algorithm.

## Peephole Optimizations
Peephole optimizations performed by the compiler include:
* Constant folding of conditionals whose left- and right-hand-side are constants into jumps.
* Constant folding of expressions that contain only constant operands.
* Elimination of a jump followed immediately by the label it jumps to.
Note that the elimination of jumps is only performed at the very end as this destroys basic blocks.

## Strength Reductions
The compiler currently reduces the following forms of instructions:
* a * 0 ==> 0 and 0 * a ==> 0
* a * 2^k ==> a << k and 2^k * a ==> a << k
* a + 0 ==> a and 0 + a ==> a and a - 0 ==> a
* a / 1 ==> a
* Expansion of a / 2^k to a combination of >> and +
Note that the expansion of division is only done for constant divisors that do not equal -1. This is to avoid silently ignoring an overflow exception that should have been caused by quotient overflow.

## Tail Recursion Optimization
We implemented a basic form of tail recursion. It checks all basic blocks with return statements for recursive function call statements immediately before said return statements, and replaces the recursive call with the necessary mov statements and an unconditional jump to the top of the function. While tail recursion can be done for mutually recursive functions, we did not have time to implement this optimization. 
The effect of this optimization would be eliminating much of the the overhead associated with function calls, including preserving caller and callee-saved-registers, and incrementing the stack pointer.

## Partial Redundancy Elimination (PRE)
PRE is implemented using the Lazy Code Motion (LCM) algorithm presented in chapter 9 of the Dragon Book. The algorithm makes use of 4 dataflow passes using the dataflow framework and has the effect of Common Subexpression Elimination (CSE), Loop Invariant Code Motion (LICM), and a stronger form of CSE that eliminates redundant expressions that are not necessarily common to all paths to the entry node.
This optimization is made more effective by copy and constant propagation as they reduce the number of distinct subexpressions. This can cause redundant subexpressions to become more transparent and aid the algorithm to catch and eliminate them. As our compiler performs PRE before our SSA optimizations that perform copy and constant propagation, a pass of local constant and copy propagation is done before LCM as an approximation.
One side effect of the LCM algorithm is that it can cause the creation of many empty blocks. This is because of critical edge splitting, which is the process of splitting edges that go to successors with more than one predecessor. This has the benefit of increasing the number of candidates for code motion, but if a block is not selected to compute any redundant expressions, then it is left as a redundant jump in the code. A CFG cleaning pass mitigates this.

## Sparse Conditional Constant Propagation
Sparse Conditional Constant Propagation (SCCP) was implemented using a modified version of the algorithm in "Constant Propagation with Conditional Branches".
This algorithm works to calculate the value of temps statically. Our implementation generates a map from temps to constants (assuming constants can be found for the temp), and substitutes that constant wherever the temp is used. Due to how we implemented function call parameters, we could not remove any instructions whose destination temps' values can be resolved to constants.
Additionally, this algorithm swaps conditional jumps whose condition can be fully resolved for an unconditional jump, and removes all un-visitable basic blocks, simplifying the CFG.
While our SCCP does not decrease the instruction count, its main purpose is to set up the program in such a way that ADCE can very easily remove useless instructions. It also has the added effect of tunring resolvable conditional jumps into non-conditional jumps, which has a variety of benefits, notably less total instructions and a simpler CFG for future optimizations (and register allocation) to deal with.

## SSA-based global copy propagation
Our implementation of global copy propagation is similar to the algorithm mentioned in lecture 2, which builds a map from every temp in the program to whichever temp is at the beginning of that temp's chain of mov instructions. It then iterates through each of the instructions of the program and replaces any used temp with its corresponding temp in the map. One thing to note is that we do not copy propagate over phi functions. If we were to propagate over phi functions, we would need to have the capability to place parallel copy instructions from SSA destruction in a specific order at the time of SSA destruction, which would require us to change our SSA translation.
While this optimization does not remove any instructions, much like SCCP, it prepares the code in such a way that ADCE can easily remove useless instructions.

## Aggressive Dead Code Elimination
Arguably the most important optimization performed by the compiler, Aggressive Dead Code Elimination (ADCE) has the effect of removing all instructions that do not affect the return value or end result of the program. This pass "empties the garbage" created and marked by previous optimization passes, and its performance is closely linked to how well the previous phases of optimization perform.
\par ADCE also removes all conditionals that do not direct control flow away from useful instructions. Our implementation was based on the algorithm given in the Cooper Book chapter 10. This results in many unreachable blocks that can be removed in a later pass.

### Liveness Analysis
The livenes analysis step allows us to inform the register allocator of which variables are live-out to each line, which it uses to construct its interference graph. There are currently two implementations of liveness analysis present in `liveinfo.ml`, but only the dataflow framework implementation is used.

The first (old) implementation uses the graph library written for interference graphs to construct a simple (reverse) control flow graph that maps each line to its predecessors. We then implement the by-variable liveness back propagation shown in the lecture notes. This proved to be slow as the analysis performs a hash table lookup for each line in the propagation step. At first we used the original `line` type given by the L1 checkpoint starter code. This proved to be unweildy as we were frequently converting the operand lists into sets and back at each iteration of the loop. We replaced this first with a `Core.Set` and then a `Core.Hashtbl` to improve the efficiency of operations on the `uses`, `defines`, and `live_out` collections during back propagation.

The new implementation makes use of the new dataflow framework, which greatly simplified the implementation into the specification of a few dataflow equations and the creation of used/def sets for each basic block. The addition of a control flow graph library based on basic blocks also meant that the hash table lookups were done on a per-block level rather than a per-line level, which provided substantial speedup over the older implementation. 

### Register Allocation
We allocate actual x86 registers (and stack positions for the spills) to the temporary registers defined by codegen, and the swap them out in the quad assembly to be passed into the x86 generator.
  * We implemented a graph library to modularize the interference graph. This proved to be useful as we also used it to model the control flow in the liveness analysis.
  * We made the operand types hashable so that they could be efficiently stored in maps.
  * To avoid assigning the same color to different pre-defined registers, we create a "register clique" in the interference graph by drawing an edge between each of the pre-defined registers. This has the added benefit of foregoing the need to pre-color verticies in the coloring algorithm.  
  * Register allocation is be encapsulated as function that takes as input a list of three-address instruction and outputs a mapping function from temporary register operands to registers.
  * After generating the register allocation map, we translate the original quad assembly to the same language, except with the temps swapped for registers. To reflect that the languages are almost exactly the same—except for a difference in what operands are allowed—we created a functor that generates three-address pseudo-assembly modules given an operand type.
  * Temps cannot be assigned as R15 or R14, as those two registers must be reserved for two-address elaboration

## Register Coalescing
For Lab 5, Register Coalescing was improved to implement George's algorithm. This ensures that coalescing nodes does not hurt the coloroability of the graph. The effect of register coalescing leads to many self-moves that can be eliminated by a peephole optimization pass.
Register coalescing also made register allocation slightly slower because of the overhead created by expanding our graph implementation. This contributes to the uptick of timed out tests on the large suites from -O1 and -O0.

### x86_64 generation:
The x86 tree datatype was created with the intention of reflecting the final asembly as closely and as simply as possible. Registers and stack positions are now explicitly sized, and instructions use size information from their operands to determine what size they should be (add q vs l to end) in the outputted assembly, they are never explicitly sized. Additionally, instead of always jumping to a spot at the end of the program to return, returns were done by copy pasting the assembly which restores callee-saved registers wherever a return was called, but this will likely change in the future. Also, three-addr temps were never assigned to registers R14 and R15, since they are reserved to be used as an extra temp for x86 commands, or as a place to store a memory address to be dereferenced. The overall translation was done by iterating through the quad instructions and casing on the operands to ensure correct end behavior. 

## Test Scripts
### run_tests.py and print_results.py
The `run_tests.py` script is used to test different combinations and orderings of compiler optimizations. It loops through a list of jobs that each have different flags to pass to `c0c` and runs the `timecompiler` script for each of them. `print_results.py` prints the multipliers from each of the generated results files.

### code_eval.py
The `code_eval.py` script was used to test the correctness of generated ARM64 assembly, as it would be prohibitively difficult to try to modify `gradecompiler` to fulfill that purpose. It takes in the directory with all of the files you want to test as an argument.
This script assumes that all typechecking steps are done correctly (which is safe to assume if it passes gradecompiler, as the behavior of the compiler should not depend on the architecture it is run on), and otherwise prints an error message if the output does not match what the message at the top of the test file states. Additionally, running this script will cause any arithmetic error to be printed in the terminal. In order to only get the error messages that signify a compiler failure, it is recommended that you write 2> /dev/null after the command used to run this script. Lastly, it is important to note that this tester will only work on a computer with an ARM64 processor.

### code_size_gcc.py, code_size.py, and code_time_tester.py
These scripts were used to generate the data for some of the graphs seen in the report. 
`code_size_gcc.py` compiles all `.c` files in a folder, links them with run411.c, uses bash `wc` to count the size of the executable, and places the data for all files and all optimization levels in a csv file called gcc_sizes.txt
`code_size.py` does the same thing as `code_size_gcc.py` except with our own compiler. Additionally, it has the capability to dest all combinations of optimizations on our level vs. `llc` and print them to a file. Lastly, has the capability to test for both -x86-64 and ARM64 depending on the flags you pass into functions.
Lastly `code_time_tester` is used to time how long the traces took to run at different optimization levels. It also takes a directory as an argument.
---

## Source Files
The following are the source files for the L4 Compiler

    README.md               -- this file

    Makefile                -- makefile for the compiler

    For a quick test:

        % make          (generates file ../bin/c0c using dune build)

        % ./bin/c0c --verbose --emit abs ./examples/return01.c0

                        should generate ../tests/return01.c0.abs in pseudo
                        assembly

        % make clean        (removes generated files)

    .merlin           The file that merlin uses for determining where build
                      artifacts are located. This is autogenerated by dune and
                      should not be committed.  Merlin is useful for
                      determining types of expressions and for autocomplete.

    ../bin/c0c        The native executable generated by the Makefile

    top.ml          This is the main driver.  It calls all the other parts
                    of the compiler.

    parse/pst.ml                  parse tree for the l4 language
    parse/ast.ml                  (elaborated) abstract syntax tree for l4 
    parse/c0_lexer.mll            lexer for l4 (ocamllex file)
    parse/c0_parser.mly           parser for l4 (menhir file)
    parse/parse.ml                code that sets up and calls the parser/lexer

    type/typechecker.ml           type checker over the ast

    ir/ir_ree.ml                  data structure representing the IR tree
    it/ir_trans.ml                converts from the AST to the IR tree

    codegen/assem.ml                               representation of assembly instruction
                                                   and operand types used by the compiler
    codegen/three_addr_trans/three_addr_trans.ml   generates pseudo-assembly with temporaries
                                                   from IR
    codegen/reg_trans/reg_trans.ml                 generates pseudo-assembly with temporaries
                                                   replaced by x86-64 registers
    codegen/two_addr_trans.ml                      generates an assembly representation that
                                                   can easily be formatted as x86-64 assembly code

    graph/graph.ml                graph library supporting directed and undirected graph operations
    graph/ssa_trans.ml            functions to construct and destruct SSA form
    graph/cfg/cfg.ml                   template library for control flow graphs
    graph/cfg/cfg_trans.ml             functions to translate three-address assembly to a CFG
    graph/coalesce/coalesce_graph.ml   algorithm to coalesce interference graph during register 
                                       allocation
    
    regalloc/liveinfo.ml          generates a liveness analysis of the pseudo-assembly
    regalloc/regalloc.ml          generates a pseudo-assembly with actual registers using the 
                                  assembly generated by codegen

    dataflow/dataflow.ml          contains dataflow framework used in several optimizations

    dominator/dominance_frontier.ml   calcualtes the dominance frontier of variables using the 
                                      dominator tree
    dominator/dominator_tree.ml       calculates the reverse dominator tree on a CFG

    optimization/constant_copy_prop.ml        module for basic copy propagation on non-SSA
    optimization/dead_code_elmin.ml           module for dead code elimination on SSA
    optimization/partial_redundancy_elim.ml   module for partial redundancy elimination
    optimization/peephole.ml                  module for basic peephole optimizations on non-SSA
    optimization/puree_analysis.ml            module for purity analysis
    optimization/scc.ml                       module for SCC on SSA
    optimization/ssa_copy_prop.ml             module for copy propagation on SSA
    optimization/tail_recursion.ml            module for tail recursion optimization on non-SSA
    
    utils/counter/counter.ml      provides a functor for types that can be generated on the fly
    utils/counter/temp.ml         generates temporary variables on the fly
    utils/counter/tempvar.ml      generates variables to combat an edge case in elaboration
    utils/counter/local_label.ml  generatese labels on the fly
    utils/error_msg.ml            error message utilities
    utils/function_timer.ml       generates a wrapper that computes the runtime of functions
    utils/mark.ml                 library for tracking source file positions
    utils/symbol.ml               symbol table library
    utils/print_utils.ml          contains printing functions for things like lists

---

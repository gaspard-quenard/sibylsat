# SibylSat

## Overview

SibylSat is an incremental SAT-based planner for totally-ordered HTN planning problems based on a fork of the [Lilotane planner](https://github.com/domschrei/lilotane). Like lilotane and other current SAT-based solver, SibylSat adheres to a standard procedure of alternating between expanding the search space, encoding it into a SAT formula, and invoking a SAT solver to find a solution plan. However, it differ from the other SAT-based planner in that it uses a greedy best first search to explore the search space instead of the usual breadth-first search. More details about the planner can be found in the [ECAI paper](insert_url_here).

### Valid Inputs

SibylSat operates on totally-ordered HTN planning problems given as HDDL files [2]. The provided HTN domain may be recursive or non-recursive.

In short, SibylSat supports exactly the HDDL specification from the International Planning Competition (IPC) 2020 provided in [3] and [4].
It handles type systems, STRIPS-style actions with positive and negative conditions, method preconditions, equality and "sort-of" constraints, and universal quantifications in preconditions and effects.
SibylSat _cannot_ handle conditional effects, existential quantifications, or any other extended formalisms going beyond the mentioned concepts.

### Output

SibylSat outputs a plan in accordance to [5]. Basically everything in between "`==>`" and "`<==`" is the found plan, and everything inside that plan in front of the word `root` is the sequence of classical actions to execute. 

## Building

You can build SibylSat like this:

```
mkdir -p build
cd build
cmake .. -DCMAKE_BUILD_TYPE=RELEASE -DIPASIRSOLVER=glucose4
make
cd ..
```

The SAT solver to link SibylSat with can be set with the `IPASIRSOLVER` variable. Valid values are `cadical`, `cryptominisat`, `glucose4`, `lingeling`, and `riss`.

Note that the Makefile in the base directory is only supposed to be used for building SibylSat [as an IPASIR application](https://github.com/biotomas/ipasir).

## Usage

SibylSat uses the HDDL file format.

Execute the planner executable like this:
```bash
./sibylsat path/to/domain.hddl path/to/problem.hddl [options]
```

By default, the executable is launched with the best sibylsat configuration. In particular, some options had been added for the sibylsat planner such as:

* `-mutex=<0|1>`: Filter possible effects of abstract tasks using mutexes. Very useful to sibylsat to find better abstract plans. Default is 1.
* `-macroActions=<0|1>`: Join consecutive actions in subtasks methods into a single macro action. Default is 1.
* `-preprocessFacts=<0|1>`: Ground the problem (using panda grounder) to find all the ground facts that can exist in the problem and restrict methods and tasks and their possible effects using those facts. Default is 1.
* `-restrictSortsInFA=<0|1>`: Restrict the sorts of the possible effects of methods to the most constrained sort. For example. If a method has a parameter of sort 'car' an call a primtive subtask with this parameter, but the parameter sort of the primitive task is vehicle (which is a super sort of car), the possible effects of the method will be restricted to the sort car. Default is 1.


You can launch the original Lilotane planner by using the following options:


```bash
./sibylsat path/to/domain.hddl path/to/problem.hddl -sibylsat=0 -mutex=0 -macroActions=0 -preprocessFacts=0 -restrictSortsInFA=0
```


Some useful parameters as well:
* `-v=<verb>`: Verbosity of the planner. Use 0 if you absolutely only care about the plan. Use 1 for warnings, 2 for general information, 3 for verbose output and 4 for full debug messages.
* `-wp`: If a plan is found, write it into plan.txt.
* `-wf`: Write the generated formula to `./f.cnf`. As SibylSat works incrementally, the formula will consist of all clauses added during program execution. Additionally, when the program exits, the assumptions used in the final SAT call will be added to the formula as well.

## License

The code of SibylSat is published under the GNU GPLv3. Consult the LICENSE file for details.  
The planner uses [pandaPIparser](https://github.com/panda-planner-dev/pandaPIparser) and [pandaPIgrounder](https://github.com/panda-planner-dev/pandaPIgrounder) [2] which are [3-Clause BSD](https://opensource.org/license/bsd-3-clause) licensed.

Note that depending on the SAT solver compiled into the planner, usage and redistribution rights may be subject to their licensing.
Specifically: CaDiCaL, Cryptominisat, Lingeling and Riss are Free Software while Glucose technically is not.

## Background and References

SibylSat is based on a fork of the Lilotane planner developed by Dominik Schreiber <dominik.schreiber@kit.edu> [1]. SibylSat itself is developed by Gaspard Quenard <gaspard.quenard@univ-grenoble-alpes.fr>

If you use SibylSat in academic work, please cite [0].

---

[0] My paper...

[1] Schreiber, D. (2021). [**Lilotane: A Lifted SAT-based Approach to Hierarchical Planning.**](https://doi.org/10.1613/jair.1.12520) In Journal of Artificial Intelligence Research (JAIR) 2021 (70), pp. 1117-1181.

[2] Behnke, G., Höller, D., Schmid, A., Bercher, P., & Biundo, S. (2020). [**On Succinct Groundings of HTN Planning Problems.**](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.090/Publikationen/2020/AAAI-BehnkeG.1770.pdf) In AAAI (pp. 9775-9784).

[3] Höller, D., Behnke, G., Bercher, P., Biundo, S., Fiorino, H., Pellier, D., & Alford, R. (2020). [**HDDL: An Extension to PDDL for Expressing Hierarchical Planning Problems.**](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.090/Publikationen/2020/Hoeller2020HDDL.pdf) In AAAI (pp. 9883-9891).

[4] Behnke, G. et al. (2020). [**HDDL - Addendum.**](http://gki.informatik.uni-freiburg.de/competition/hddl.pdf) Universität Freiburg.

[5] Behnke, G. et al. (2020). [**Plan verification.**](http://gki.informatik.uni-freiburg.de/ipc2020/format.pdf) Universität Freiburg.

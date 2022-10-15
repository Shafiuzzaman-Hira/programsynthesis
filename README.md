# Program Synthesis to Exploit Algorithmic DoS Attack
An attacker can exploit algorithmic DoS attack by leveraging worst
performance of an algorithm with seemingly innocuous inputs. Hence,
generating worst performance inputs becomes a vital step to test the
reliability of a software system. Research approaches targeting per-
formance behavior of the systems triggered by the worst performance
inputs are very rare. While there is an extensive amount of literature
can be found on worst-case complexity analysis, approaches target-
ing synthesize inputs that trigger worst-performance of a system is
very rare. This paper aims to generate worst performance inputs us-
ing program synthesis technique. The novelty of our approach is it
does not depend on user defined resource bound or complex algorithm
like genetic programs. Instead, it solely depends on carefully con-
structed cost model and a SMT solver. We empirically evaluate our
approach by implementing program synthesis technique that gener-
ates inputs to exploit resource-intensive branches of a program. Our
synthesized worst performance inputs are analogous to most interest-
ing input seeds of AFL fuzzer since it explores the deepest program
paths. Experimental result shows that our synthesized worst perfor-
mance inputs significantly improve the cover


## Use the following command to run the program
```
python3 toycompiler.py
```

The are several example specifications (s1, s2, s3, s4) and output example (o1,o2) added in the repository. 
You can also find some synthsized solutions (r1,r2,r3) for each of the specifications 

1. COMPILATION

The executable file ShareInfer.jar should work just fine. If you want to compile a new jar file then use the following commands:

1.0 At the working folder share_infer, create a new folder "binfiles" using: 
    "mkdir binfiles"
    
1.1 At the working folder share_infer, compiling all the files in src/ and store them into binfiles using: 
   "javac src/*.java -d binfiles"
   
1.2 Go to binfiles directory using:
   "cd binfiles"
   
1.3 Create jar file with MainSolver as the main class using:
   "jar cfe newSolver.jar MainSolver *.class"
   
1.4 Move newSolver.jar to the working directory using:
   "mv newSolver.jar .."
   
2. RUNNING EXAMPLES

There are two modes:

2.1 Demo mode: simply type "java -jar solver.jar -demo" to run all examples in the example folder

2.2 Single mode: type "java -jar solver.jar inputFile outputFile" to run example in inputFile and store the result into outputFile

For example, "java -jar solver.jar bi_list1 result"

3. EXAMPLE FORMAT  

First line: Either "UNIFORM", "UNIFORM tree" "PRECISE" or "BIABDUCTION" where "tree" is a specific tree to check for uniformity (otherwise the solver will guess).

Second line (optional): Recursive predicate declaration. It has the form "REC pred_name:=formula"

Third line: The formula that needs to check for uniformity or precise. If the query is BIABDUCTION then it is the antecedent formula

Fourth line: The consequent formula if the query is BIABDUCTION

4. OUTPUT FORMAT

Besides the proofs search that is printed on the screen, the solver also write its result into the given outputFile

If the query is UNIFORM or PRECISE: the first line is YES/NO/UNKNOWN or ANY(if the formula is uniform for any tree, e.g., EMP). The second line is the running time in seconds.

If the query is BIABDUCTION: the first line is the anti-frame, the second file is the inference-frame and the third line is the running time in seconds.

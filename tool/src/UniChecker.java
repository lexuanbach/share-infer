//This class is to check whether a formula is uniform
public class UniChecker {
	
	//Constant declaration
	public static final int YES = 1;
	public static final int NO = 2;
	public static final int UNKNOWN = 3;
	public static final int ANY = 4;
	
	//Internal data structure declaration
	
	//Keep track whether the inductive hypothesis was declared.
	//Initial value is false and it is set to true when induction is applied
	public boolean hypothesis = false;
	//When the induction hypothesis is set to be true, its guard condition is also set to be true,
	//which means the hypothesis cannot be applied immediately.
	//The guard only becomes false once we are able to split the goal formula into smaller fragments
	public boolean hypothesisGuard = true;
	public STree hypothesisTree = new STree();
	public static int goalID = 0;
	
	public UniChecker(){}
	
	//Check whether f is t-uniform. The result is either YES, NO or UNKNOWN
	//We also assume that the formula itself is satisfiable
	public int checkUniform(Formula f, STree t){
		
		System.out.println("Checking " + f + " |-- " + "UNIFORM(" + t + ") ...\n");
		
		Formula uni = new Formula(new Property(t));
		String tail = " |-- " + uni;
		
		if (f.type == Formula.MAP || f.type == Formula.MAP2){
			System.out.println("Apply MAP-RULE for " + f + tail);
			if (t.equals(f.frac)){
				System.out.println("DONE");
				return YES;
			} else {
				System.out.println("CONTRADICTION");
				return NO;	
			}
		}
		
		if (f.type == Formula.OR){
			System.out.println("Apply OR-RULE for " + f + tail);
			int first = goalID++;
			int second = goalID++;
			System.out.println("Split goal into two subgoals: G" + first + " AND G" + second);
			System.out.println("G" + first + ": " + f.leftF + tail);
			System.out.println("G" + second + ": " + f.rightF + tail + "\n");
			System.out.println("\nProof for G" + first + ":\n");
			int result1 = checkUniform(f.leftF,t);
			//If the first proof fails, return it as the result
			if (result1 == UNKNOWN || result1 == NO) return result1;
			
			System.out.println("\nProof for G" + second + ":\n");
			int result2 = checkUniform(f.rightF,t);
			if (result1 == YES && result2 == YES)
				return YES;
			else if (result1 == UNKNOWN || result2 == UNKNOWN)
				return UNKNOWN;
			else return NO;
		}
		
		if (f.type == Formula.AND){
			System.out.println("Apply AND-RULE for " + f + tail);
			int first = goalID++;
			int second = goalID++;
			System.out.println("Split goal into two subgoals: G" + first + " OR G" + second);
			System.out.println("G" + first + ": " + f.leftF + tail);
			System.out.println("G" + second + ": " + f.rightF + tail + "\n");
			System.out.println("\nProof for G" + first + ":\n");
			int result = checkUniform(f.leftF,t);
			
			if (result == YES) return YES;
			
			System.out.println("\nFail to prove G" + first + ". Try to prove G" + second + ":\n");
			result = checkUniform(f.rightF,t);
			if (result == YES)return YES;
			
			System.out.println("Fail to prove G" + second + ". TERMINATE.");
			return UNKNOWN;
		}
		
		if (f.type == Formula.STAR){
			if ((hypothesis == true && hypothesisGuard == true) && 
					(((f.leftF.type == Formula.MAP || f.leftF.type == Formula.MAP2) && f.leftF.frac.equals(hypothesisTree)) || 
					 ((f.rightF.type == Formula.MAP || f.rightF.type == Formula.MAP2) && f.rightF.frac.equals(hypothesisTree)))){
				System.out.println("Detect " + hypothesisTree + "-smaller-fragments of the current formula");
				System.out.println("Apply STAR-RULE with induction guard off for " + f + tail);
				System.out.println("Set inductive hypothesis guard to False");
				hypothesisGuard = false;
			} else {
				System.out.println("Apply STAR-RULE for " + f + tail);
			}
			int first = goalID++;
			int second = goalID++;
			System.out.println("Split goal into two subgoals: G" + first + " AND G" + second);
			System.out.println("G" + first + ": " + f.leftF + tail);
			System.out.println("G" + second + ": " + f.rightF + tail + "\n");

			System.out.println("\nProof for G" + first + ":\n");
			int result1 = checkUniform(f.leftF,t);
			//The the first proof fails, return it as the result
			if (result1 == NO || result1 == UNKNOWN) return result1;
			
			System.out.println("\nProof for G" + second + ":\n");
			int result2 = checkUniform(f.rightF,t);
			if (result1 == YES && result2 == YES)
				return YES;
			else return UNKNOWN;
		}
		
		if (f.type == Formula.EMP || f.type == Formula.EQ || f.type == Formula.PROP){
			System.out.println("Apply EMP-RULE for " + f + tail);
			System.out.println("DONE");
			return YES;
		}
		
		if (f.type == Formula.REC){
			if (hypothesis == true && hypothesisGuard == false){
				System.out.println("Apply INDUCTIVE-HYPOTHESIS <" + f.recPred.id + tail + "> for " + f + tail);
				System.out.println("DONE");
				return YES;
			}
			
			if (hypothesis == false){
				System.out.println("Apply STRONG-INDUCTION for " + f + tail);
				System.out.println("Hypothesis: " + f.recPred.id + tail);
				System.out.println("Set inductive hypothesis guard to True");
				System.out.println("Choose the hypothesis guard tree to be " + t);
				hypothesisTree = t.cloneTree();
				hypothesis = true;
				hypothesisGuard = true;
				return checkUniform(f.recF,t);
			}

		}
		
		if (f.type == Formula.EXT){
			System.out.println("Apply EX-ELIMINATION-RULE for " + f + tail);
			System.out.println("Change goal to " + f.internalF + tail + "\n");
			return checkUniform(f.internalF,t);
		}
		
		// If goal is t <.> P |-- UNIFORM (t) then we replace it with
		// P |-- UNIFORM (BLACK)
		//Could be made more general by supporting factorization
		if (f.type == Formula.DOT && f.dotFrac.equals(t)){
			System.out.println("Apply DOT-POS-RULE for " + f + tail);
			String newTail = " |-- " + (new Property(new STree(STree.BLACK)));
			System.out.println("Change goal to " + f.dotF + newTail);
			return checkUniform(f.dotF,new STree(STree.BLACK));
		}
				
		return UNKNOWN;
	}
	
	//Reset the values after each run
	public void reset(){
		hypothesis = false;
		hypothesisGuard = true;
		hypothesisTree = new STree();
		goalID = 0;
	}
	
	//Find a good candidate for uniformity and check whether f is uniform with respect to the found value
	public Pair<Integer,STree> findUniform(Formula f){

		if (f.type == Formula.MAP || f.type == Formula.MAP2){
			System.out.println("The formula " + f + " is " + f.frac.cloneTree() + "-UNIFORM");
			return new Pair<Integer,STree>(new Integer(YES),f.frac.cloneTree());
		}
		if (f.type == Formula.EQ || f.type == Formula.EMP || f.type == Formula.PROP){
			System.out.println("The formula " + f + " is t-UNIFORM for any t");
			return new Pair<Integer,STree>(new Integer(ANY),new STree());
		}			
			
		STree candidate = findSTree(f);
		if (candidate.type == STree.ERROR){
			System.out.println("Fail to find a tree candidate. TERMINATE.");
		} else{
			System.out.println("Find a candidate tree: " + candidate);
			System.out.println("Check whether " + f + " |-- " + (new Formula(new Property(candidate))) + "\n");
			int result = checkUniform(f,candidate);
			if (result == YES){
				System.out.println("\nThe formula " + f + " is " + candidate + "-UNIFORM");
				return new Pair<Integer,STree>(YES, candidate.cloneTree());
			} 
		}

		System.out.println("UNKNOWN");
		return new Pair<Integer,STree>(UNKNOWN, new STree());
	}
	
	//Find the first fractional tree share in the formula, from left to right
	public STree findSTree(Formula f){
		
		STree candidate = new STree();
		
		if (f.type == Formula.MAP || f.type == Formula.MAP2)
			return f.frac.cloneTree();
		
		if (f.type == Formula.AND || f.type == Formula.OR || f.type == Formula.IMP || f.type == Formula.STAR){
			candidate = findSTree(f.leftF);
			//If we fail to find a tree from the left formula,
			//then we look for it in the right formula
			if (candidate.type == STree.ERROR)
				candidate = findSTree(f.rightF);
		}
		
		if (f.type == Formula.REC)
			candidate = findSTree(f.recF);
		
		if (f.type == Formula.NEG || f.type== Formula.ALL || f.type == Formula.EXT)
			candidate = findSTree(f.internalF);
		
		return candidate;
	}
}

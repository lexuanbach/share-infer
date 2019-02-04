//This class is to check whether a formula is precise
//using the rules for precisely(P)
public class PreciseChecker {
	
	//Constant declaration
	public static final int YES = 1;
	public static final int NO = 2;
	public static final int UNKNOWN = 3;
	
	//Internal data structure declaration
	
	public boolean hypothesis = false;
	//When the induction hypothesis is set to be true, its guard condition is also set to be true,
	//which means the hypothesis cannot be applied immediately.
	//The guard only becomes false once we are able to split the goal formula into smaller fragments
	public boolean hypothesisGuard = true;
	
	public static int goalID = 0;
	
	public PreciseChecker(){}
	
	public String printPreciseFormula(Formula f){
		return (new Formula(Formula.TSTAR,f)).toString() + " |-- " + (new Property(f)).toString();
	}
	
	//Check whether the formula f is precisely
	//The result is either YES, NO or UNKNOWN
	public int checkPrecisely(Formula goal){
		
		if (goal.type == Formula.EMP || goal.type == Formula.EQ || goal.type == Formula.PROP){
			System.out.println("Apply PRECISELY-EMP-RULE for: " + printPreciseFormula(goal));
			System.out.println("DONE\n");
			return YES;
		}
		
		if (goal.type == Formula.MAP || goal.type == Formula.MAP2){
			System.out.println("Apply PRECISELY-MAP-RULE for: " + printPreciseFormula(goal));
			System.out.println("DONE\n");
			return YES;
		}
		
		if (goal.type == Formula.AND){
			System.out.println("Apply PRECISELY-AND-RULE for: " + printPreciseFormula(goal));
			int first = ++goalID;
			int second = ++goalID;
			System.out.println("Split goal into two subgoals: G" + first + " OR G" + second);
			System.out.println("G" + first + ": " + printPreciseFormula(goal.leftF));
			System.out.println("G" + second + ": " + printPreciseFormula(goal.rightF) + "\n");
			System.out.println("Proof for G" + first);
			int result = checkPrecisely(goal.leftF);
			if (result == YES) return YES;
			
			System.out.println("Fail to prove G" + first + ". Try to prove G" + second);
			result = checkPrecisely(goal.rightF);
			if (result == YES) return YES;
			
			System.out.println("Fail to prove G" + second + ". TERMINATE.");
			return UNKNOWN;
			}

		if (goal.type == Formula.OR && isConflicted(goal.leftF,goal.rightF)){
			System.out.println("Detect conflicts in: " + goal.leftF + " and " + goal.rightF);
			System.out.println("Apply PRECISELY-OR-RULE for: " + printPreciseFormula(goal));
			
			int first = ++goalID;
			int second = ++goalID;
			System.out.println("Split goal into two subgoals: G" + first + " AND G" + second);
			System.out.println("G" + first + ": " + printPreciseFormula(goal.leftF));
			System.out.println("G" + second + ": " + printPreciseFormula(goal.rightF) + "\n");
			System.out.println("Proof for G" + first);
			int result1 = checkPrecisely(goal.leftF);
			System.out.println("Proof for G" + second);
			int result2 = checkPrecisely(goal.rightF);
			
			if (result1 == YES && result2 == YES)
				return YES;
			
			return UNKNOWN;
		}
		
		if (goal.type == Formula.STAR){
			System.out.println("Apply PRECISELY-STAR for: " + printPreciseFormula(goal));
			
			int first = ++goalID;
			int second = ++goalID;
			
			if ((hypothesis == true && hypothesisGuard == true) && 
					(isSmallerFragment(goal.leftF) || isSmallerFragment(goal.rightF))){
				System.out.println("Detect smaller fragments inside: " + goal);
				System.out.println("Set inductive hypothesis guard to False\n");
				hypothesisGuard = false;
			}
			
			System.out.println("Split goal into two subgoals: G" + first + " AND G" + second);
			System.out.println("G" + first + ": " + printPreciseFormula(goal.leftF));
			System.out.println("G" + second + ": " + printPreciseFormula(goal.rightF) + "\n");
			
			
			System.out.println("Proof for G" + first);
			int result1 = checkPrecisely(goal.leftF);
			System.out.println("Proof for G" + second);
			int result2 = checkPrecisely(goal.rightF);
			
			if (result1 == YES && result2 == YES)
				return YES;
			
			return UNKNOWN;
			
		}
		/*
		if (f.type == Formula.ALL){
			System.out.println("Apply PRECISELY-ALL for " + f);
			System.out.println("Change goal into " + f.internalF);
			return checkPrecisely(f.internalF);
		}
		*/
		if (goal.type == Formula.EXT && isUnique(goal,goal.var)){
			System.out.println("Detect uniqueness condition for <" + goal.var + "> in: " + goal.internalF);
			System.out.println("Apply PRECISELY-EXT for: " + printPreciseFormula(goal));
			System.out.println("Change goal into: " + printPreciseFormula(goal.internalF) + "\n");
			return checkPrecisely(goal.internalF);
		}
		/*
		if (goal.type == Formula.TSTAR){
			
			Formula iF = goal.starF;
			
			if (iF.type == Formula.EQ || iF.type == Formula.EMP || iF.type == Formula.PROP || 
				iF.type == Formula.MAP || iF.type == Formula.MAP2){
				return checkPrecisely(iF);
			}
			
			if (iF.type == Formula.STAR || iF.type == Formula.AND || iF.type == Formula.OR){
				Formula f1 = new Formula(Formula.TSTAR,iF.leftF);
				Formula f2 = new Formula(Formula.TSTAR,iF.rightF);
				return checkPrecisely(new Formula(iF.type,f1,f2));
			}
			
			if (iF.type == Formula.EXT || iF.type == Formula.ALL){
				Formula f = new Formula(Formula.TSTAR,iF.internalF);
				return checkPrecisely(new Formula(iF.type,iF.var,f));
			}
			
			return UNKNOWN;			
		}
		*/
		if (goal.type == Formula.REC){
			
			if (hypothesis == true && hypothesisGuard == false){
				System.out.println("Apply INDUCTIVE-HYPOTHESIS <" + printHypothesis(goal) + "> for: " + printPreciseFormula(goal));
				System.out.println("DONE\n");
				return YES;
			}
			
			if (hypothesis == false){
				System.out.println("Apply STRONG-INDUCTION for G" + goalID + ": " + printPreciseFormula(goal));
				System.out.println("Hypothesis: " + printHypothesis(goal));
				System.out.println("Set hypothesis guard to be True\n");
				hypothesis = true;
				hypothesisGuard = true;
				System.out.println("Unfold G" + goalID + " into: " + printPreciseFormula(goal.recF) + "\n");
				return checkPrecisely(goal.recF);
			}
			
			return UNKNOWN;
		}
		
		if (goal.type == Formula.DOT){
			System.out.println("Apply DOT-POS-RULE for: " + printPreciseFormula(goal));
			System.out.println("Change goal into: " + printPreciseFormula(goal.dotF));
			return checkPrecisely(goal.dotF);
		}
		
		return UNKNOWN;
	}
	
	public void reset(){
		goalID = 0;
		hypothesis = false;
		hypothesisGuard = true;
	}
	
	//Check whether f(x) AND f(y) |- x = y
	public boolean isUnique(Formula f, Term var){
		
		if (var.type == Term.VAR){
			if (f.type == Formula.EXT)
				return isUnique(f.internalF,var);
				
			if (f.type == Formula.MAP){
				if (var.equals(f.rightTerm) || var.equals(f.rightTerm2))
					return true;
			}
			
			if (f.type == Formula.MAP2){
				if (var.equals(f.rightTerm) || var.equals(f.rightTerm2) || var.equals(f.rightTerm3))
					return true;
			}
			
			if (f.type == Formula.STAR){
				return isUnique(f.leftF,var) || isUnique(f.rightF,var);
			}
		}
		
		return false;
	}
	
	
	//Check whether f1 * f2 |- False (return True)
	//False otherwise (satisfiable or unknown)
	public boolean isConflicted(Formula f1, Formula f2){
		
		if (f1.type == Formula.MAP || f1.type == Formula.MAP2){
			if (f2.type == Formula.EQ && f2.leftTerm.equals(f1.leftTerm) && f2.rightTerm.equals(new Term()))
				return true;
			// Maybe also handle the case MAP * MAP
		}
		
		if (f2.type == Formula.MAP || f2.type == Formula.MAP2){
			if (f1.type == Formula.EQ && f1.leftTerm.equals(f2.leftTerm) && f1.rightTerm.equals(new Term()))
				return true;
		}
		
		if (f1.type == Formula.STAR){
			return isConflicted(f1.leftF,f2) || isConflicted(f1.rightF,f2);
		}
		
		if (f2.type == Formula.STAR){
			return isConflicted(f1,f2.leftF) || isConflicted(f1,f2.rightF);
		}
		
		if(f1.type == Formula.EXT){
			return isConflicted(f1.internalF,f2);
		}
		
		if (f2.type == Formula.EXT){
			return isConflicted(f1,f2.internalF);
		}
		
		return false;
	}
	
	//Check whether the formula f is strictly non empty
	public boolean isSmallerFragment(Formula f){
		
		if (f.type == Formula.TSTAR){
			int iType = f.starF.type;
			if (iType == Formula.MAP || iType == Formula.MAP2)
				return true;
		}
		
		if (f.type == Formula.MAP || f.type == Formula.MAP2)
			return true;
		
		return false;
	}
	
	public String printHypothesis(Formula f){
		
		if (f.type == Formula.REC){
			return "TRUE * " + f.recPred.id + " |-- " + "PRECISELY (" + f.recPred.id + ")";
		}
		
		return "Error in method Precise.Checker.printHypothesis()!";
	}
}

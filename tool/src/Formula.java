//Formula construction
//import java.util.*;
public class Formula {
	
	//Constant declaration
	public static final int AND = 1;
	public static final int OR = 2;
	public static final int IMP = 3;
	public static final int NEG = 4;
	public static final int STAR = 5;
	public static final int MAP = 6;
	public static final int MAP2 = 7;
	public static final int EQ = 8;
	public static final int EMP = 9;
	public static final int SINGLE = 10;
	public static final int ALL = 11;
	public static final int EXT = 12;
	public static final int PRED = 13;
	public static final int PROP = 14;
	public static final int TSTAR = 15; //special formula T * F for proving precisely
	public static final int DOT = 16;
	
	
	public static final int REC = 100;
	
	//Internal data declaration
	
	public int type;
	
	//For SINGLE
	public boolean truth;
	
	//For AND, OR, IMP, STAR: leftF op rightF
	public Formula leftF,rightF;
	
	//For NEG,ALL,EXT: neg internalF | ALL var internalF | EXT var internalF
	public Formula internalF;
	public Term var;
	
	//For MAP: leftTerm --frac--> (rightTerm,rightTerm2) 
	//and MAP2: leftTerm --frac--> (rightTerm,rightTerm2,rightTerm3)
	//and EQ: leftTerm = rightTerm
	public Term leftTerm,rightTerm,rightTerm2,rightTerm3;
	public STree frac;
	
	//For PRED, single predicate
	public Predicate pred;
	
	//For REC, recursive predicate:
	public Predicate recPred;
	public Formula recF;
	
	//For TSTAR
	public Formula starF;
	
	//For PROP
	public Property prop;
	
	//For DOT
	public Formula dotF;
	public STree dotFrac;
	
	//Lists of constructors for Formula

	public Formula(){
		this.type = EMP;
	}
	
	public Formula(boolean input){
		this.type = SINGLE;
		this.truth = input;
	}
	
	public Formula(Term left,Term right){
		this.type = EQ;
		this.leftTerm = left.cloneTerm();
		this.rightTerm = right.cloneTerm();
	}
	
	public Formula(Term left,Term right1,Term right2,STree t){
		this.type = MAP;
		this.leftTerm = left.cloneTerm();
		this.rightTerm = right1.cloneTerm();
		this.rightTerm2 = right2.cloneTerm();
		this.frac = t.cloneTree();
	}
	
	public Formula(Term left,Term right1,Term right2,Term right3,STree t){
		this.type = MAP2;
		this.leftTerm = left.cloneTerm();
		this.rightTerm = right1.cloneTerm();
		this.rightTerm2 = right2.cloneTerm();
		this.rightTerm3 = right3.cloneTerm();
		this.frac = t.cloneTree();
	}
	
	public Formula(Formula f){
			this.type = NEG;
			this.internalF = f.cloneFormula();	
	}
	
	public Formula(int type, Term var, Formula f){
		if ((type == ALL || type == EXT) && var.type == Term.VAR){
			this.type = type;
			this.var = var.cloneTerm();
			this.internalF = f.cloneFormula();
		}
	}
	
	public Formula(int type,Formula left,Formula right){
		if (type == AND || type == OR || type == STAR || type == IMP){
			this.type = type;
			this.leftF = left.cloneFormula();
			this.rightF = right.cloneFormula();
		} else{
			System.out.println("Error in the Formula constructor!");
		}
	}
	
	public Formula(Predicate pred){
		this.type = PRED;
		this.pred = pred.clonePredicate();
	}
	
	public Formula(Predicate recPred,Formula recF){
		this.type = REC;
		this.recPred = recPred.clonePredicate();
		this.recF = recF.cloneFormula();
	}
	
	public Formula(Property prop){
		this.type = PROP;
		this.prop = prop.cloneProperty();
	}
	
	public Formula(int type, Formula f){
		if (type == TSTAR){
			this.type = TSTAR;
			this.starF = f.cloneFormula();
		}
	}
	
	public Formula(STree dotFrac, Formula f){
		this.type = DOT;
		this.dotFrac = dotFrac.cloneTree();
		this.dotF = f.cloneFormula();
	}
	
	public Formula cloneFormula(){
		if (type == EMP) return new Formula();
		if (type == SINGLE) return new Formula(truth);
		if (type == EQ) return new Formula(leftTerm,rightTerm);
		if (type == MAP) return new Formula(leftTerm,rightTerm,rightTerm2,frac);
		if (type == MAP2) return new Formula(leftTerm,rightTerm,rightTerm2,rightTerm3,frac);
		if (type == NEG) return new Formula(internalF.cloneFormula());
		if (type == ALL || type == EXT) return new Formula(type,var,internalF.cloneFormula());
		if (type == AND || type == OR || type == STAR || type == IMP) 
			return new Formula(type,leftF.cloneFormula(),rightF.cloneFormula());
		if (type == REC) return new Formula(recPred,recF);
		if (type == PRED) return new Formula(pred);
		if (type == PROP) return new Formula(prop);
		if (type == TSTAR) return new Formula(STAR,starF);
		if (type == DOT) return new Formula(dotFrac,dotF);
		
		System.out.println("Error in the method Formula.cloneFormula()!");
		return new Formula();
	}
	
	public String toString(){
		if (type == EMP) return "EMP";
		if (type == SINGLE){
			if (truth) return "TRUE";
			else return "FALSE";
		}
		if (type == EQ) return "(" + leftTerm + ")" + " = " + "(" + rightTerm + ")";
		if (type == MAP) 
			return "(" + leftTerm + ")" +  " |--" + frac + "--> (" + rightTerm + "," + rightTerm2 + ")";
		if (type == MAP2)
			return "(" + leftTerm + ")" + " |--" + frac + "--> (" + rightTerm + "," + rightTerm2 + "," + rightTerm3 + ")";
		if (type == NEG) return "NEG " + var + " " + internalF;
		if (type == ALL) return "ALL (" + var + ") (" + internalF + ")";
		if (type == EXT) return "EXT (" + var + ") (" + internalF + ")";
		if (type == AND) return "(" + leftF + ")" + " AND " + "(" + rightF + ")";
		if (type == OR) return "(" + leftF + ")" + " OR " + "(" + rightF + ")";
		if (type == IMP) return "(" + leftF + ")" + " IMP " + "(" + rightF + ")";
		if (type == STAR) return "(" + leftF + ")" + " * " + "(" + rightF + ")";
		if (type == REC) return recPred.toString();
		if (type == PRED) return pred.toString();
		if (type == PROP) return prop.toString();
		if (type == TSTAR) return "TRUE * " + starF;
		if (type == DOT) return "(" + dotFrac + ")" + " <.> " + "(" + dotF + ")";
		
		return "Error in method Formula.toString()!";
	}
}

//This class is to Construct the anti-frame F1 and inference frame F2 in
// F1 * A |-- F2 * B

import java.util.ArrayList;

public class BiAbductor {

	//Constant declaration
	public static final String prefixFresh = "fresh";
	public static final int NOTFOUND = -1;
	public static final int CONTRADICTION = -2;
	public static final int FOUND = 1;
	public static final int RECDEPTH = 10; // Maximal unfold depth level
	//Internal data structure declaration

	static int countFresh = 0;
	//Remember the recursive id and its formulas to unfold
	Predicate recPredicate = new Predicate();
	Formula recFormula = new Formula();
	static int recDepth = RECDEPTH;
	ArrayList<Formula> goalFormula = new ArrayList<Formula>();
	boolean isPrecise = false;
	int isUniform = UniChecker.UNKNOWN;
	STree uTree = new STree();
	
	
	//List of constructors
	public BiAbductor(){}
	
	//Construct pair (F1,F2) s.t.
	//premiseF * F1 |- goalF and F2 is the remaining of premiseF after subtracting F1, i.e.
	//F1 * F2 |- premiseF * F1
	public Pair<Formula,ArrayList<Formula>> abduct(Formula premiseF, Formula goalF){
		
		ArrayList<Formula> premises = starFlatten(premiseF);
		ArrayList<Formula> eqList = new ArrayList<Formula>();
		ArrayList<Formula> antiList = new ArrayList<Formula>();
		Pair<Formula,ArrayList<Formula>> result;
		Formula contraF = new Formula(false);
		int foundIndex = NOTFOUND;
		
		if (goalF.type == Formula.MAP || goalF.type == Formula.MAP2 
				|| goalF.type == Formula.PRED || goalF.type == Formula.EQ
				|| (goalF.type == Formula.DOT && goalF.dotF.type == Formula.PRED)){
			foundIndex = lookUp(goalF,premises);
			
			if (foundIndex == CONTRADICTION) {
				System.out.println("Found a contradiction while contructing anti-frame for " + goalF + ". TERMINATE!");
				return new Pair<Formula,ArrayList<Formula>>(contraF,eqList);
			}
			
			if (foundIndex == NOTFOUND) {
				goalFormula.add(goalF.cloneFormula());
				for (int i = 0 ; i < goalFormula.size(); i++) {
					goalFormula.set(i, listSubstitute(goalFormula.get(i),eqList));
				}
				System.out.println("Found anti-frame for " + goalF + ": " + goalF);
				return new Pair<Formula,ArrayList<Formula>>(goalF.cloneFormula(),eqList);
			}
			
			if (foundIndex >= 0){
				for (int i = 0 ; i < goalFormula.size(); i++) {
					goalFormula.set(i, listSubstitute(goalFormula.get(i),eqList));
				}
				return simpleAbduct(premises.get(foundIndex),goalF);
			}

		}
		
		if (goalF.type == Formula.OR){
			System.out.println("Goal is in OR form. Construct anti-frame for the first sub-formula " + goalF.leftF);
			result = abduct(premiseF,goalF.leftF);
			if (isFalse(result.first)){
				System.out.println("Fail to construct anti-frame for " + goalF.leftF);
				System.out.println();
				System.out.println("Construct anti-frame for the second sub-formula " + goalF.rightF);
				return abduct(premiseF,goalF.rightF);
			}
			
			//System.out.println("Found the anti-frame for " + goalF.leftF + ": " + printFrame(result.first,result.second));
			return result;
		}
		
		if (goalF.type == Formula.STAR) {
			System.out.println("Goal is in STAR form. Construct anti-frame for the first sub-formula " + goalF.leftF);
			result = abduct(premiseF,goalF.leftF);
			if (isFalse(result.first)){
				System.out.println("Found a contradiction while contructing anti-frame for " + goalF.leftF + ". TERMINATE!");
				return new Pair<Formula,ArrayList<Formula>>(contraF,eqList);
			}
			
			//System.out.println("Found the antiframe for " + goalF.leftF + ": " + printFrame(result.first,result.second));
			antiList.add(result.first);
			eqList.addAll(result.second);
			Formula newGoalF = listSubstitute(goalF,result.second);
			if (result.second.size() > 0) {
				System.out.println("Substitute equalities " + result.second + " in anti-frame into goal");
				System.out.println("Update goal into " + newGoalF);				
			}
			System.out.println();
			System.out.println("Construct anti-frame for the second sub-formula " + newGoalF.rightF);
			Pair<Formula,ArrayList<Formula>> newResult = abduct(premiseF,newGoalF.rightF);
			if (isFalse(newResult.first)){
				System.out.println("Found a contradiction while contructing anti-frame for " + newGoalF.rightF + ". TERMINATE!");
				return new Pair<Formula,ArrayList<Formula>>(new Formula(false),eqList);
			}
			
			if (newResult.first.type != Formula.EMP){
				antiList.add(newResult.first);
			}

			eqList.addAll(newResult.second);
			
			//Accumulate the fragments of anti-frame
			Formula antiFrame = starForm(antiList);

			//Update the goalFormula
			for (int i = 0 ; i < goalFormula.size(); i++) {
				goalFormula.set(i, listSubstitute(goalFormula.get(i),eqList));
			}

			//System.out.println("Remove all fresh equalities in anti-frame: " + eqList);
			return new Pair<Formula,ArrayList<Formula>>(antiFrame,eqList);	
		}
		
		if (goalF.type == Formula.REC){	
			
			foundIndex = lookUp(goalF,premises);
			
			if (foundIndex == CONTRADICTION){
				System.out.println("Found a contradiction while contructing anti-frame for " + goalF + ". TERMINATE!");
				return new Pair<Formula,ArrayList<Formula>>(new Formula(false),eqList);
			}
			
			if (foundIndex >= 0){
				// Change to B <.> P
				if (premises.get(foundIndex).type == Formula.DOT){
					goalF = new Formula(new STree(STree.BLACK),goalF);
				} else{
					System.out.println("Found a perfect match in antecedent for " + goalF);
					System.out.println("Derive the trivial anti-frame for " + goalF + ": " + (new Formula()));
					goalFormula.add(goalF.cloneFormula());
					return new Pair<Formula,ArrayList<Formula>>(new Formula(),eqList);					
				}

			}
			
			if (foundIndex == NOTFOUND){
				System.out.println("Cannot find a match for recursive predicate " + goalF);
				System.out.println("Unfold " + goalF);
				System.out.println();
				//If this is the first time to unfold, remember the predicate id and its formula
				if (recDepth == RECDEPTH) {
					recPredicate = goalF.recPred.clonePredicate();
					recFormula = goalF.recF.cloneFormula();
					
					System.out.println("Try to prove precise(" + goalF + ") using precisely");
					System.out.println();
					PreciseChecker pChecker = new PreciseChecker();
					if (pChecker.checkPrecisely(goalF) == PreciseChecker.YES){
						System.out.println("Recursive predicate " + goalF + " is precise");
						System.out.println("Unlock DOT-PLUS-RULE for " + goalF.recPred.id + ": (a+b) <.> " + goalF.recPred.id 
								+ "(X) |-- " + "a <.> " + goalF.recPred.id + "(X) * b <.> " + goalF.recPred.id + "(X)");
						isPrecise = true;
					}
					System.out.println();
					System.out.println("Try to prove uniformity for " + goalF);
					System.out.println();
					UniChecker uChecker = new UniChecker();
					Pair<Integer,STree> pResult = uChecker.findUniform(goalF);
					if (pResult.first == UniChecker.YES){
						System.out.println("Recursive predicate " + goalF + " is UNIFORM(" + pResult.second + ")");
						isUniform = UniChecker.YES;
						uTree= pResult.second.cloneTree();
					}
					
					if (pResult.first == UniChecker.ANY){
						System.out.println("Recursive predicate " + goalF + " is UNIFORM(p) for any p");
						isUniform = UniChecker.ANY;
						uTree= pResult.second.cloneTree();
						System.out.println("Unlock DOT-STAR-RULE for " + goalF.recPred.id + ": p <.> (" + goalF + "(X) * " 
						+ goalF + "(Y)) --||-- p <.> " + goalF + "(X) * p <.> " + goalF + "(Y)");
					}
					
					System.out.println();
					System.out.println("Resuming back to the goal. After unfolding");
					
				}
				//If this is not the first time but still within the allowed depth
				if (recDepth > 0 && recDepth < RECDEPTH ) {
					goalF.recF = recFormula.cloneFormula();
					for (int i = 0; i < goalF.recPred.numArgs; i++) {
						goalF.recF = substitute(goalF.recF,recPredicate.args[i].var,goalF.recPred.args[i].var);
					}
				}
				
				recDepth--;

				System.out.println("Try to construct the anti-frame for " + goalF.recF);
				System.out.println();
				return abduct(premiseF,goalF.recF);
			}
		}
		
		if (goalF.type == Formula.EXT){
			String freshVar= prefixFresh + countFresh++;
			System.out.println("Goal is in EXISTENTIAL form. Initiate <" + goalF.var + "> with temporary fresh variable <" + freshVar + ">");
			Formula newGoalF = substitute(goalF.internalF,goalF.var.var,freshVar);
			System.out.println("Change goal into " + newGoalF);
			System.out.println();
			Pair<Formula,ArrayList<Formula>> tempResult = abduct(premiseF,newGoalF);
			//Update goalFormula
			for (int i = 0;i < goalFormula.size();i++){
				goalFormula.set(i,listSubstitute(goalFormula.get(i),tempResult.second));
			}
			filterEqList(tempResult.second);
			//System.out.println("Remove fresh equalities from the anti-frame");
			return tempResult;
		}
		
		if (goalF.type == Formula.DOT && goalF.dotF.type == Formula.REC){
			foundIndex = lookUp(goalF,premises);
			
			if (foundIndex == CONTRADICTION){
				System.out.println("Found a contradiction while contructing anti-frame for " + goalF + ". TERMINATE!");
			}
			
			if (foundIndex >= 0){
				return simpleAbduct(premises.get(foundIndex),goalF);
			}
			
			if (foundIndex == NOTFOUND){
				System.out.println("Fail to find a match for " + goalF);
				System.out.println("Unfold " + goalF.dotF + " and apply DOT-POS-RULE with share " + goalF.dotFrac);
				System.out.println();	
				
				//If this is the first time to unfold, remember the predicate id and its formula
				if (recDepth == RECDEPTH) {
					recPredicate = goalF.dotF.recPred.clonePredicate();
					recFormula = goalF.dotF.recF.cloneFormula();

					System.out.println("Try to prove precise(" + goalF.dotF + ") using precisely");
					System.out.println();
					PreciseChecker pChecker = new PreciseChecker();
					if (pChecker.checkPrecisely(goalF.dotF) == PreciseChecker.YES){
						System.out.println("Recursive predicate " + goalF.dotF + " is precise");
						System.out.println("Unlock DOT-PLUS-RULE for " + goalF.dotF.recPred.id + ": (a+b) <.> " + goalF.dotF.recPred.id 
								+ "(X) |-- " + "a <.> " + goalF.dotF.recPred.id + "(X) * b <.> " + goalF.dotF.recPred.id + "(X)");
						isPrecise = true;
					}
					pChecker.reset();
					System.out.println();
					System.out.println("Try to prove uniformity for " + goalF.dotF);
					System.out.println();
					UniChecker uChecker = new UniChecker();
					Pair<Integer,STree> pResult = uChecker.findUniform(goalF.dotF);
					if (pResult.first == UniChecker.YES){
						System.out.println("Recursive predicate " + goalF.dotF + " is UNIFORM(" + pResult.second + ")");
						isUniform = UniChecker.YES;
						uTree= pResult.second.cloneTree();
						System.out.println("Unlock DOT-STAR-RULE for " + goalF.dotF.recPred.id + ": p <.> (" + goalF.dotF + "(X) * " 
						+ goalF.dotF + "(Y)) --||-- p <.> " + goalF.dotF + "(X) * p <.> " + goalF.dotF + "(Y)");
					}
					
					if (pResult.first == UniChecker.ANY){
						System.out.println("Recursive predicate " + goalF.dotF + " is UNIFORM(p) for any p");
						isUniform = UniChecker.ANY;
						uTree= pResult.second.cloneTree();
					}
					uChecker.reset();
					System.out.println();
					System.out.println("Resuming back to the goal. After unfolding");
				}
				//If this is not the first time but still within the allowed depth
				if (recDepth > 0 && recDepth < RECDEPTH ) {
					goalF.dotF.recF = recFormula.cloneFormula();
					for (int i = 0; i < goalF.dotF.recPred.numArgs; i++) {
						goalF.dotF.recF = substitute(goalF.dotF.recF,recPredicate.args[i].var,goalF.dotF.recPred.args[i].var);
					}
				}
				
				recDepth--;
				
				Formula newGoalF = applyStarPos(goalF.dotF.recF,goalF.dotFrac);
				System.out.println("Change goal into " + newGoalF);
				System.out.println();
				return abduct(premiseF,newGoalF);
			}
		}

	
		System.out.println("Fail to construct the anti-frame for " + goalF + ". TERMINATE!");
		return new Pair<Formula,ArrayList<Formula>>(new Formula(false),eqList);
	}
	
	//Remove equalities with fresh variables
	public void filterEqList(ArrayList<Formula> eqList) {
		int num = eqList.size();
		for (int i = 0; i < num; i++) {
			if (eqList.get(i).leftTerm.var.startsWith(prefixFresh)) {
				eqList.remove(i--);
				num--;
			}
		}
	}
	
	public Formula listSubstitute(Formula f, ArrayList<Formula> eqList){
		Formula result = f.cloneFormula();
		for (int i = 0;i < eqList.size();i++){
			Formula tempF = eqList.get(i);
			if (tempF.type == Formula.EQ && tempF.leftTerm.type == Term.VAR && tempF.rightTerm.type != Term.NULL){
				result = substitute(result,tempF.leftTerm.var,tempF.rightTerm.var);
			}
		}
		
		return result;
	}
	
	public Formula printFrame(Formula f, ArrayList<Formula> eqList){
		Formula result = f.cloneFormula();
		for (int i = 0; i < eqList.size(); i++){
			result = new Formula(Formula.STAR,result,eqList.get(i));
		}
		result = simplify(result);
		return result;
	}
	
	public boolean isFalse(Formula f){
		return f.type == Formula.SINGLE && f.truth == false;
	}
	//Abduction for the case MAP, MAP2, PRED and DOT with the assumption that
	//f1 and f2 are already matched
	public Pair<Formula,ArrayList<Formula>> simpleAbduct(Formula f1,Formula f2) {
		
		STree antiShare = new STree(STree.WHITE);
		Formula antiFrame = new Formula(); // the default value of antiFrame is EMP
		ArrayList<Formula> eqList = new ArrayList<Formula>();
		if (f1.type == f2.type) {

			if (f1.type == Formula.EQ && f1.leftTerm.equals(f2.leftTerm) && f1.rightTerm.equals(f2.rightTerm)){
				System.out.println("Found anti-frame for the formula " + f2 + ": " + printFrame(new Formula(),eqList));
				goalFormula.add(f2.cloneFormula());
				return new Pair<Formula,ArrayList<Formula>>(new Formula(),eqList);	
			}
			
			if (f1.type == Formula.MAP && f1.leftTerm.equals(f2.leftTerm)) {
				antiShare = f2.frac.substract(f1.frac);
				if (!f1.rightTerm.equals(f2.rightTerm))
					eqList.add(new Formula(f2.rightTerm,f1.rightTerm));
				if (!f1.rightTerm2.equals(f2.rightTerm2))
					eqList.add(new Formula(f2.rightTerm2,f1.rightTerm2));
				//If antiShare is not empty then update antiFrame
				if (!antiShare.equals(new STree(STree.WHITE)))
					antiFrame = new Formula(f1.leftTerm,f1.rightTerm,f1.rightTerm2,antiShare);
				System.out.println("Found anti-frame for the formula " + f2 + ": " + printFrame(antiFrame,eqList));
				goalFormula.add(f2);
				return new Pair<Formula,ArrayList<Formula>>(antiFrame,eqList);		
			}
			
			if (f1.type == Formula.MAP2 && f1.leftTerm.equals(f2.leftTerm)) {
				antiShare = f2.frac.substract(f1.frac);
				if (!f1.rightTerm.equals(f2.rightTerm))
					eqList.add(new Formula(f2.rightTerm,f1.rightTerm));
				if (!f1.rightTerm2.equals(f2.rightTerm2))
					eqList.add(new Formula(f2.rightTerm2,f1.rightTerm2));
				if (!f1.rightTerm3.equals(f2.rightTerm3))
					eqList.add(new Formula(f2.rightTerm3,f1.rightTerm3));
				//If antiShare is not empty then update antiFrame
				if (!antiShare.equals(new STree(STree.WHITE)))
					antiFrame = new Formula(f1.leftTerm,f1.rightTerm,f1.rightTerm2,f1.rightTerm3,antiShare);
				System.out.println("Found anti-frame for the formula " + f2 + ": " + printFrame(antiFrame,eqList));
				goalFormula.add(f2);
				return new Pair<Formula,ArrayList<Formula>>(antiFrame,eqList);		
			}
			
			if (f1.type == Formula.DOT) {

				if (f1.dotF.type == f2.dotF.type && f1.dotF.type == Formula.PRED 
						&& f1.dotF.pred.id.equals(f2.dotF.pred.id)) {
					antiShare = f2.dotFrac.substract(f1.dotFrac);
					for (int i = 0;i < f1.dotF.pred.numArgs;i++) {
						if (!f1.dotF.pred.args[i].equals(f2.dotF.pred.args[i]))
							eqList.add(new Formula(f2.dotF.pred.args[i],f1.dotF.pred.args[i]));
					}
					if (!antiShare.equals(new STree(STree.WHITE)))
						antiFrame = new Formula(antiShare,f1.dotF.cloneFormula());
					System.out.println("Found anti-frame for the formula " + f2 + ": " + printFrame(antiFrame,eqList));
					goalFormula.add(f2);
					return new Pair<Formula,ArrayList<Formula>>(antiFrame,eqList);
				}

				if (f1.dotF.type == f2.dotF.type && f1.dotF.type == Formula.REC 
						&& f1.dotF.recPred.id.equals(f2.dotF.recPred.id)) {
					antiShare = f2.dotFrac.substract(f1.dotFrac);
					for (int i = 0;i < f1.dotF.recPred.numArgs;i++) {
						if (!f1.dotF.recPred.args[i].equals(f2.dotF.recPred.args[i]))
							eqList.add(new Formula(f2.dotF.recPred.args[i],f1.dotF.recPred.args[i]));
					}
					//Need precise as one of the conditions
					if (!antiShare.equals(new STree(STree.WHITE))) {
						if (isPrecise) {
							antiFrame = new Formula(antiShare,f1.dotF.cloneFormula());
							System.out.println("Found anti-frame for the formula " + f2 + "using DOT-PLUS-RULE: " + printFrame(antiFrame,eqList));
						} else {
							System.out.println("Found a match for " + f2 + ": " + f1 + ". But the precicate is not precise. TERMINATE!");
							return new Pair<Formula,ArrayList<Formula>>(new Formula(false),eqList);
						}

					} else {
						System.out.println("Found anti-frame for the formula " + f2 + ": " + printFrame(antiFrame,eqList));
					}

					goalFormula.add(f2);
					return new Pair<Formula,ArrayList<Formula>>(antiFrame,eqList);
				}
			}
			
			if (f1.type == Formula.PRED && f1.dotF.pred.id.equals(f2.dotF.pred.id) 
					&& f1.dotF.pred.numArgs == f2.dotF.pred.numArgs) {
				for (int i = 0;i < f1.dotF.pred.numArgs;i++) {
					if (!f1.dotF.pred.args[i].equals(f2.dotF.pred.args[i]))
						eqList.add(new Formula(f2.dotF.pred.args[i],f1.dotF.pred.args[i]));
				}
				System.out.println("Found anti-frame for the formula " + f2 + ": " + printFrame(antiFrame,eqList));
				goalFormula.add(f2);
				return new Pair<Formula,ArrayList<Formula>>(antiFrame,eqList);
			}
			
			//Return f2 as default result
			System.out.println("Found anti-frame for the formula " + f2 + ": " + printFrame(f2.cloneFormula(),eqList));
			goalFormula.add(f2);
			return new Pair<Formula,ArrayList<Formula>>(f2.cloneFormula(),eqList);
		}
		
		if (f1.type == Formula.DOT && f2.type != Formula.DOT){
			return simpleAbduct(f1,new Formula(new STree(STree.BLACK),f2));
		}
		
		if (f1.type != Formula.DOT && f2.type == Formula.DOT){
			return simpleAbduct(new Formula(new STree(STree.BLACK),f1),f2);
		}
		
		System.out.println("Error in method BiAbductor.simpleAbduct()");
		return new Pair<Formula,ArrayList<Formula>>(new Formula(false),eqList);

	}
	
	//Simplify f by grouping permissions of the same predicate or remove extra EMP
	public Formula simplify(Formula f){
		ArrayList<Formula> listF = starFlatten(f);
		//System.out.println(listF);
		int listSize = listF.size();
		
		for (int i = 0;i < listSize;i++){
			Formula currentF = listF.get(i);
			
			if (currentF.type == Formula.MAP){
				for (int j = i+1;j < listSize;j++){
					Formula tempF = listF.get(j);
					if (tempF.type == Formula.MAP && currentF.leftTerm.equals(tempF.leftTerm)
							&& currentF.rightTerm.equals(tempF.rightTerm) && currentF.rightTerm2.equals(tempF.rightTerm2)){
						if(!currentF.frac.joinable(tempF.frac)) {
							System.out.println("Found a contradiction while trying to join " + currentF.frac + " with " + tempF.frac);
							return new Formula(false);
						} else {
							STree sumFrac = currentF.frac.join(tempF.frac);
							Formula sumF = new Formula(currentF.leftTerm,currentF.rightTerm,currentF.rightTerm2,sumFrac);
							listF.set(i,sumF); // Update the current formula
							listF.remove(j); // Remove the extra map
							//Update the index values
							j--;
							listSize--;	
						}
					}
				}	
			}
			
			if (currentF.type == Formula.MAP2){
				for (int j = i+1;j < listSize;j++){
					Formula tempF = listF.get(j);
					if (tempF.type == Formula.MAP2 && currentF.leftTerm.equals(tempF.leftTerm)
							&& currentF.rightTerm.equals(tempF.rightTerm) && currentF.rightTerm2.equals(tempF.rightTerm2)
							&& currentF.rightTerm3.equals(tempF.rightTerm3)){
						if(!currentF.frac.joinable(tempF.frac)) {
							System.out.println("Found a contradiction while trying to join " + currentF.frac + " with " + tempF.frac);
							return new Formula(false);
						} else{
							STree sumFrac = currentF.frac.join(tempF.frac);
							Formula sumF = new Formula(currentF.leftTerm,currentF.rightTerm,currentF.rightTerm2,currentF.rightTerm3,sumFrac);
							listF.set(i,sumF); // Update the current formula
							listF.remove(j); // Remove the extra map
							//Update the index values
							j--;
							listSize--;
						}
					}
				}	
			}
			
			if (currentF.type == Formula.DOT && currentF.dotF.type == Formula.REC){
				for (int j = i+1;j < listSize;j++){
					Formula tempF = listF.get(j);
					if (tempF.type == Formula.DOT && tempF.dotF.type == Formula.REC  && currentF.dotF.recPred.equals(tempF.dotF.recPred)){
						if(!currentF.dotFrac.joinable(tempF.dotFrac)) {
							System.out.println("Found a contradiction while trying to join " + currentF.frac + " with " + tempF.frac);
							return new Formula(false);
						} else{
							STree sumFrac = currentF.dotFrac.join(tempF.dotFrac);
							Formula sumF;
							if (sumFrac.equals(new STree(STree.BLACK))){
								sumF = currentF.dotF.cloneFormula();
							} else{
								sumF = new Formula(sumFrac,currentF.dotF);
							}

							listF.set(i,sumF); // Update the current formula
							listF.remove(j); // Remove the extra map
							//Update the index values
							j--;
							listSize--;
						}
					}
				}	
			}
			
			if (currentF.type == Formula.EMP){
				listF.remove(i);
				listSize--;
				i--;
			}
			
			if (currentF.type == Formula.DOT && currentF.dotFrac.equals(new STree(STree.BLACK))){
				listF.set(i, currentF.dotF);
			}
		}
		
		return starForm(listF);
	}
	
	public Formula starForm(ArrayList<Formula> listF){
		
		if (listF.size() == 0) return new Formula();
		
		//Remove duplicates
		int num = listF.size();
		for (int i = 0;i < num;i++){
			for (int j = i+1;j < num;j++){
				if((listF.get(i).type == Formula.EQ && listF.get(j).type == Formula.EQ) && 
				    listF.get(i).leftTerm.equals(listF.get(j).leftTerm) && 
				    listF.get(i).rightTerm.equals(listF.get(j).rightTerm)){
					listF.remove(j--);
					num--;
				}
			}
		}
		
		Formula result = listF.get(0);
		for (int i = 1;i < listF.size();i++){
			result = new Formula(Formula.STAR,result,listF.get(i));
		}
		
		return result;
	}
	
	//Reset internal values after each run
	public void reset(){
		countFresh = 0;
		recPredicate = new Predicate();
		recFormula = new Formula();
		recDepth = RECDEPTH;
		goalFormula = new ArrayList<Formula>();
		isPrecise = false;
		isUniform = UniChecker.UNKNOWN;
		uTree = new STree();
	}
	//Combine two methods abduct and infer into a single on
	public Pair<Formula,Formula> biAbduct(Formula antecedentF, Formula consequentF){
		reset(); // reset all internal data structures
		System.out.println("Starting the bi-abduction process");
		System.out.println("Antecedent: " + antecedentF);
		System.out.println("Consequent: " + consequentF);
		System.out.println();
		System.out.println("Try to simplify the antecedent and consequent");
		Formula newAnte = simplify(antecedentF);
		Formula newCon = simplify(consequentF);
		System.out.println("New antecedent: " + newAnte);
		System.out.println("New consequent: " + newCon);
		System.out.println();
		System.out.println("Start the abduction process. Finding anti-frame ....\n");
		Pair<Formula,ArrayList<Formula>> result = abduct(newAnte,newCon);
		
		Formula antiF = new Formula(false);
		Formula inferF = new Formula(false);
		
		if (result.first.type == Formula.SINGLE && result.first.truth == false){
			System.out.println("Fail to find the anti-frame. TERMINATE!");
			return new Pair<Formula,Formula>(new Formula(false),new Formula(false));
		} else {
			//System.out.println(result);
			antiF = simplify(printFrame(result.first,result.second));
			if (antiF.type == Formula.SINGLE && antiF.truth == false) {
				System.out.println("Found a contradiction while constructing anti-frame. TERMINATE!");
				return new Pair<Formula,Formula>(new Formula(false),new Formula(false));
			}
			
			System.out.println("Successfully found the anti-frame: " + antiF);
			System.out.println();
			
			newAnte = simplify(new Formula(Formula.STAR,newAnte,printFrame(result.first,result.second)));
			
			if (newAnte.type == Formula.SINGLE && newAnte.truth == false){
				System.out.println("Found a contradiction while updating the antecedent. TERMINATE!");
				return new Pair<Formula,Formula>(new Formula(false),new Formula(false));
			}
			
			System.out.println("Update the antecedent: " + newAnte);
			System.out.println();

			if (goalFormula.size() > 0){
				newCon = simplify(starForm(goalFormula));
			}
			
			if (newCon.type == Formula.SINGLE && newCon.truth == false){
				System.out.println("Found a contradiction while updating the consequent. TERMINATE!");
				return new Pair<Formula,Formula>(new Formula(false),new Formula(false));
			}
			
			System.out.println("Update the consequent: " + newCon);		
			System.out.println();


			System.out.println("Start the inference process. Finding the inference-frame ...\n");
			inferF = infer(newAnte,newCon);
			
			if (inferF.type == Formula.SINGLE && inferF.truth == false){
				System.out.println("Fail to find the inference-frame. TERMINATE!");
				return new Pair<Formula,Formula>(new Formula(false),new Formula(false));
			} else{
				System.out.println("Successfully found the inference-frame: " + inferF);
				System.out.println();
				System.out.println("Antecedent: " + antecedentF);
				System.out.println("Consesequent: " + consequentF);
				System.out.println("Anti-frame: " + antiF);
				System.out.println("Inference-frame: " + inferF);
				return new Pair<Formula,Formula>(antiF,inferF);
			}
			
		}
	}
	
	//Construct the frame F s.t.
	//f1 |- F * f2
	public Formula infer(Formula antecedentF, Formula consequentF){
		//System.out.println(antecedentF + "    " + consequentF);
		
		//If abduct was called before, we will take advantage of the derived goal stored in the program

		if (goalFormula.size() > 0){
			Formula newConsequentF = starForm(goalFormula);
			goalFormula = new ArrayList<Formula>(); //Reset the goal
			return infer(antecedentF,newConsequentF);
		}
		
		ArrayList<Formula> anteList = starFlatten(antecedentF);
		ArrayList<Formula> conList = starFlatten(consequentF);
		
		for (int i = 0;i < conList.size();i++){
			//System.out.println(anteList);
			int foundIndex = lookUp(conList.get(i),anteList);
			if (foundIndex == NOTFOUND || foundIndex == CONTRADICTION){
				System.out.println("Fail to derive " + conList.get(i) + ". TERMINATE!");
				return new Formula(false);
			}
			if (foundIndex >= 0){
				Formula tempConF = conList.get(i);
				Formula tempAnteF = anteList.get(foundIndex);
				
				if (tempConF.type == Formula.EMP){
					System.out.println("Current sub-goal is " + tempConF + ". The inference is trivial.\n");
				}
				
				if (tempConF.type == Formula.EQ || tempConF.type == Formula.PRED || tempConF.type == Formula.REC){
					//Change to B <.> P and move to the Formula.DOT type below
					if (tempAnteF.type == Formula.DOT){
						tempConF = new Formula(new STree(STree.BLACK),tempConF);
					} else{
						System.out.println("Found a perfect match for " + tempConF + " in the antecedent");
						System.out.println("Remove " + tempConF + " from the antecedent\n");
						anteList.remove(foundIndex);
					}
				}
				
				if (tempConF.type == Formula.DOT){
					//Change from P to B <.> P for compatible type
					if (tempAnteF.type != Formula.DOT) tempAnteF = new Formula(new STree(STree.BLACK),tempAnteF);
					STree resFrac = tempAnteF.dotFrac.substract(tempConF.dotFrac);
					if (resFrac.equals(new STree(STree.WHITE))){
						System.out.println("Found a perfect match for " + tempConF + " in the antecedent");
						System.out.println("Remove " + tempAnteF + " from the antecedent\n");
						anteList.remove(foundIndex);
					} else {
						
						Formula resF = new Formula(resFrac,tempAnteF.dotF);
						
						System.out.println("Found a match for " + tempConF + " in the antecedent: " + tempAnteF);
						System.out.println("Replace " + tempAnteF + " in antecedent with " + resF + "\n");
						anteList.set(foundIndex, resF);	
						
					}
				}
				
				if (tempConF.type == Formula.MAP){
					STree resFrac = tempAnteF.frac.substract(tempConF.frac);
					if (resFrac.equals(new STree(STree.WHITE))){
						System.out.println("Found a perfect match for " + tempConF + " in the antecedent");
						System.out.println("Remove " + tempConF + " from the antecedent\n");
						anteList.remove(foundIndex);
					} else{
						Formula resF = new Formula(tempAnteF.leftTerm,tempAnteF.rightTerm,tempAnteF.rightTerm2,resFrac);
						System.out.println("Found a match for " + tempConF + " in the antecedent: " + tempAnteF);
						System.out.println("Replace " + tempAnteF + " in antecedent with " + resF + "\n");
						anteList.set(foundIndex, resF);	
						
					}
				}
				
				if (tempConF.type == Formula.MAP2){
					STree resFrac = tempAnteF.frac.substract(tempConF.frac);
					if (resFrac.equals(new STree(STree.WHITE))){
						System.out.println("Found a perfect match for " + tempConF + " in the antecedent");
						System.out.println("Remove " + tempConF + " from the antecedent\n");
						anteList.remove(foundIndex);
					} else {
						Formula resF = new Formula(tempAnteF.leftTerm,tempAnteF.rightTerm,tempAnteF.rightTerm2,tempAnteF.rightTerm3,resFrac);
						System.out.println("Found a match for " + tempConF + " in the antecedent: " + tempAnteF);
						System.out.println("Replace " + tempAnteF + " in antecedent with " + resF + "\n");
						anteList.set(foundIndex, resF);		
					}
			
				}
			}
		}
		
		//All matched
		if (anteList.size() == 0) return new Formula();
		//Else return the residue inside the antecedent
		else {
			Formula result = anteList.get(0);
			for (int i = 1;i < anteList.size();i++){
				result = new Formula(Formula.STAR,result,anteList.get(i));
			}
			
			return result;
		}
	}
	
	
	//Distribute frac into frac <.> f
	public Formula applyStarPos(Formula f, STree frac){
		
		if (f.type == Formula.EMP || f.type == Formula.EQ || f.type == Formula.PROP || f.type == Formula.SINGLE)
			return f.cloneFormula();
		
		if (f.type == Formula.MAP){
			return new Formula(f.leftTerm,f.rightTerm,f.rightTerm2,f.frac.treeMul(frac).cloneTree());
		}
		
		if (f.type == Formula.MAP2){
			return new Formula(f.leftTerm,f.rightTerm,f.rightTerm2,f.rightTerm3,f.frac.treeMul(frac).cloneTree());
		}
		
		if (f.type == Formula.EXT || f.type == Formula.ALL)
			return new Formula(f.type,f.var,applyStarPos(f.internalF,frac));
		
		if (f.type == Formula.AND || f.type == Formula.OR) {
			return new Formula(f.type,applyStarPos(f.leftF,frac),applyStarPos(f.rightF,frac));
		}
		
		if (f.type == Formula.STAR && sameUni(f.leftF,f.rightF)){
			return new Formula(f.type,applyStarPos(f.leftF,frac),applyStarPos(f.rightF,frac));
		}
		
		if (f.type == Formula.DOT){
			return applyStarPos(f.dotF,f.dotFrac.treeMul(frac));
		}
		
		if (f.type == Formula.PRED || f.type == Formula.REC){
			return new Formula(frac,f);
		}
		
		System.out.println("Error in method BiAbductor.applyStarPos()!");
		return new Formula(false);
	}
	
	public Pair<Integer,STree> getUni(Formula f){
		if (f.type == Formula.EMP || f.type == Formula.EQ || f.type == Formula.SINGLE) {
			return new Pair<Integer,STree>(UniChecker.ANY,new STree());
		} else if (f.type == Formula.MAP || f.type == Formula.MAP2) {
			return new Pair<Integer,STree>(UniChecker.YES,f.frac.cloneTree());
		} else if (f.type == Formula.REC) {
			if (isUniform == UniChecker.ANY) {
				return new Pair<Integer,STree>(UniChecker.ANY,new STree());
			} else if (isUniform == UniChecker.YES) {
				return new Pair<Integer,STree>(UniChecker.YES,uTree.cloneTree());
			}
		} else if (f.type == Formula.DOT) {
			Pair<Integer,STree> temp = getUni(f.dotF);
			return new Pair<Integer,STree>(temp.first,temp.second.treeMul(f.dotFrac));
		} else if (f.type == Formula.STAR) {
			Pair<Integer,STree> temp1 = getUni(f.leftF);
			Pair<Integer,STree> temp2 = getUni(f.rightF);
			if (temp1.first == UniChecker.ANY) {
				return temp2;
			} else if (temp1.first == temp2.first && temp1.second.equals(temp2.second)) {
				return temp1;
			}
		}
		
		return new Pair<Integer,STree>(UniChecker.UNKNOWN,new STree());
	}
	
	//Check whether f1 and f2 have the same uniformity
	public boolean sameUni(Formula f1,Formula f2) {
			Pair<Integer,STree> result1 = getUni(f1);
			Pair<Integer,STree> result2 = getUni(f2);
			//System.out.println(result1 + "  " + result2);
			if (result1.first == UniChecker.ANY) {
				return result2.first == UniChecker.ANY || result2.first == UniChecker.YES;
			} else if (result1.first == UniChecker.YES) {

				return result2.first == UniChecker.ANY || (result2.first == UniChecker.YES && result1.second.equals(result2.second));
			}
		return false;
			
	}
	
	//Look for matching pattern of f in listF
	//If found then retrieve the index of the matched element in listF
	public int lookUp(Formula f, ArrayList<Formula> listF){
		
		for (int i = 0;i < listF.size(); i++){
			int result = isMatched(f,listF.get(i)); 
			if (result == CONTRADICTION)return CONTRADICTION;
			if (result == FOUND) return i;
		}
		
		return NOTFOUND; //Not found
	}
	
	//Check whether f1 and f2 have the same pattern
	//Assumption: both of them are quantifier-free
	public int isMatched(Formula f1,Formula f2){
		
		if (f1.type == f2.type){
			
			if (f1.type == Formula.EMP)
				return FOUND;
			
			if (f1.type == Formula.EQ){
				if (f1.leftTerm.equals(f2.leftTerm) && f1.rightTerm.equals(f2.rightTerm))
					return FOUND;

				return NOTFOUND;
			}
			
			if (f1.type == Formula.MAP || f1.type == Formula.MAP2){
				if (f1.leftTerm.type == Term.VAR && f2.leftTerm.type == Term.VAR)	
					if (f1.leftTerm.var.equals(f2.leftTerm.var))return FOUND; 
					else return NOTFOUND;
				if (f1.leftTerm.type == Term.VALUE && f2.leftTerm.type == Term.VALUE)
					if (f1.leftTerm.val == f2.leftTerm.val) return FOUND;
					else return NOTFOUND;
			}
			//The recursion case
			if (f1.type == Formula.REC)
				if (f1.recPred.id.equals(f2.recPred.id) && f1.recPred.numArgs == f2.recPred.numArgs) {
					for (int i = 0; i < f1.recPred.numArgs;i++) {
						if (!f1.recPred.args[i].equals(f2.recPred.args[i])) {
							return NOTFOUND;
						}
					}
					return FOUND;
				}
			
			if (f1.type == Formula.PRED)
				if (f1.pred.id.equals(f2.pred.id) && f1.pred.numArgs == f2.pred.numArgs) {
					for (int i = 0; i < f1.recPred.numArgs;i++) {
						if (!f1.recPred.args[i].equals(f2.recPred.args[i])) {
							return NOTFOUND;
						}
					}
					return FOUND;
				}
			
			if (f1.type == Formula.DOT)
				return isMatched(f1.dotF,f2.dotF);
			
			if (f1.type == Formula.AND || f1.type == Formula.OR || f1.type == Formula.IMP || f1.type == Formula.STAR){
				if (isMatched(f1.leftF,f2.leftF) == FOUND  && isMatched(f1.rightF,f2.rightF) == FOUND)
					return FOUND;
				if (isMatched(f1.leftF,f2.rightF) == FOUND  && isMatched(f1.rightF,f2.leftF) == FOUND)
					return FOUND;
				
				return NOTFOUND;
			}
			
			if (f1.type == Formula.NEG)
				return isMatched(f1.internalF,f2.internalF);
			
		}
		
		if ((f1.type == Formula.MAP || f1.type == Formula.MAP2) && f2.type == Formula.EQ){
			if ((f1.leftTerm.equals(f2.leftTerm) && f2.rightTerm.type == Term.NULL) || 
				 (f1.leftTerm.equals(f2.rightTerm) && f2.leftTerm.type == Term.NULL)){
				return CONTRADICTION;
			}
		}
		
		if (f1.type == Formula.EQ && (f2.type == Formula.MAP || f2.type == Formula.MAP2)){
			return isMatched(f2,f1);
		}
		
		if ((f2.type == Formula.DOT) && (f1.type != Formula.DOT)){
			return isMatched(new Formula(new STree(STree.BLACK),f1),f2);
		}
		
		if ((f1.type == Formula.DOT) && (f2.type != Formula.DOT)){
			return isMatched(f1,new Formula(new STree(STree.BLACK),f2));
		}
				
		return NOTFOUND;
	}
	
	//Substitute instances of var1 in f with var2
	public Formula substitute(Formula f, String var1, String var2){
		
		Term term1 = new Term(var1);
		Term term2 = new Term(var2);
		Formula resultF = f.cloneFormula();
		
		if (f.type == Formula.EQ){
			if (f.leftTerm.equals(term1)) resultF.leftTerm = term2;
			if (f.rightTerm.equals(term1)) resultF.rightTerm = term2;
		}
		
		if (f.type == Formula.MAP){
			if (f.leftTerm.equals(term1)) resultF.leftTerm = term2;
			if (f.rightTerm.equals(term1)) resultF.rightTerm = term2;
			if (f.rightTerm2.equals(term1)) resultF.rightTerm2 = term2;
		}
		
		if (f.type == Formula.MAP2){
			if (f.leftTerm.equals(term1)) resultF.leftTerm = term2;
			if (f.rightTerm.equals(term1)) resultF.rightTerm = term2;
			if (f.rightTerm2.equals(term1)) resultF.rightTerm2 = term2;
			if (f.rightTerm3.equals(term1)) resultF.rightTerm3 = term2;			
		}
		
		if (f.type == Formula.PRED){
			for (int i = 0;i < f.pred.numArgs;i++)
				if (f.pred.args[i].equals(term1)) resultF.pred.args[i] = term2;
		}
		
		if (f.type == Formula.AND || f.type == Formula.OR || f.type == Formula.IMP || f.type == Formula.STAR){
			return new Formula(f.type,substitute(f.leftF,var1,var2),substitute(f.rightF,var1,var2));
		}
		
		if (f.type == Formula.NEG)
			return new Formula(substitute(f.internalF,var1,var2));
		
		if ((f.type == Formula.ALL || f.type == Formula.EXT) && !f.var.equals(term1)){		
			Formula tempF = f.cloneFormula();
			//If quantifier var v is the same as t2, change v into new fresh variable
			if (f.var.equals(term2)){
				String freshVar = prefixFresh + countFresh++;
				tempF.var = new Term(freshVar);
				tempF.internalF = substitute(tempF.internalF,var2,freshVar);
			} 
				
			return new Formula(f.type,tempF.var,substitute(tempF.internalF,var1,var2));					
		}

		if (f.type == Formula.DOT)
			return new Formula(f.dotFrac,substitute(f.dotF,var1,var2));
		
		if (f.type == Formula.REC){
			Predicate tempPred = f.recPred.clonePredicate();
			for (int i = 0;i < tempPred.numArgs;i++)
				if (tempPred.args[i].equals(term1)) tempPred.args[i] = term2;
			return new Formula(tempPred, substitute(f.recF,var1,var2));
		}	
		
		return resultF;
	}
	
	// If f = A1 * A2 * ... * An then we return the list 
	//[A1,A2,...,An] as result
	public ArrayList<Formula> starFlatten(Formula f){
		
		if (f.type == Formula.STAR){
			ArrayList<Formula> list1 = starFlatten(f.leftF);
			ArrayList<Formula> list2 = starFlatten(f.rightF);
			for (int i = 0;i < list2.size();i++){
				list1.add(list2.get(i));
			}
			return list1;
		}
		
		ArrayList<Formula> list = new ArrayList<Formula>();
		list.add(f.cloneFormula());
		return list;
	}
}

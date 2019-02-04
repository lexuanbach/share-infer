//This class is to parse the formula from/to text file

import java.util.ArrayList;
import java.util.StringTokenizer;

public class FormulaParser {
	
	public static final int NOTFOUND = -1;
	public static final int ILLFORMED = -2;
	
	
	Formula recFormula = new Formula(false);
	String recID;
	boolean setRecFormula = false;
	
	//Find the first index of the operator and the string that represents the operator
	//Assumption: formula is in the right format
	public Pair<Integer,String> findNextOp(String formula){
		
		boolean initialSet = false;
		int bracketCount = 0;
		
		for (int i = 0;i < formula.length();i++){
			if (formula.charAt(i) == '('){
				initialSet = true;
				bracketCount++;
			}
			if (formula.charAt(i) == ')'){
				bracketCount--;
				if (bracketCount < 0){
					System.out.println("Formula is ill-formed. TERMINATE");
					return new Pair<Integer,String>(ILLFORMED,"");
				}
				if (bracketCount == 0 && initialSet == true){
					String subFormula = formula.substring(i + 2);
					if(subFormula.startsWith("|--")) {
						int endArrow = subFormula.indexOf("-->");
						return new Pair<Integer,String>(i+1,subFormula.substring(0, endArrow + 3));
					}
					StringTokenizer tokens = new StringTokenizer(formula.substring(i+1)," ");
					if (tokens.hasMoreTokens()){
						return new Pair<Integer,String>(i+1,tokens.nextToken());
					}
				}
			}
			
		}
		
		
		return new Pair<Integer,String>(NOTFOUND,"");
	}
	
	public STree parseTree(String tree) {
		//System.out.println(tree);
		if (tree.startsWith(" ")) return parseTree(tree.trim());
		if (tree.startsWith("(") && tree.endsWith(")")) return parseTree(tree.substring(1,tree.length()-1));
		if (tree.equals("B")){
			return new STree(STree.BLACK);
		}
		if (tree.equals("W")) {
			return new STree(STree.WHITE);
		}
		//Trim [ and ]
		String trimTree = tree.substring(2, tree.length()-2);
		int bracketCount = 0;
		
		for (int i = 0;i < trimTree.length();i++) {
			if(trimTree.charAt(i) == '[') {
				bracketCount++;
			}
			
			if(trimTree.charAt(i) == ']') {
				bracketCount--;
			}
			
			if (bracketCount < 0) {
				System.out.println("False to parse the tree " + tree);
				return new STree();
			}
			
			if (bracketCount == 0) {
				STree leftTree = parseTree(trimTree.substring(0, i+1));
				STree rightTree = parseTree(trimTree.substring(i+2));
				return new STree(leftTree,rightTree);
			}
			
		}
			
		System.out.println("Fail to parse the tree " + tree);
		return new STree();
	}
	
	public Term parseTerm(String term){
		if (term.startsWith(" ")) return parseTerm(term.trim());
		if (term.startsWith("(") && term.endsWith(")")) term = term.substring(1,term.length()-1);
		StringTokenizer tokens = new StringTokenizer(term, " ");
		while (tokens.hasMoreTokens()){
			String currentToken = tokens.nextToken();
			if (currentToken.equals("VAR") && tokens.hasMoreTokens()){
				return new Term(tokens.nextToken());
			}
			if (currentToken.equals("VAL") && tokens.hasMoreTokens()){
				int value = Integer.parseInt(tokens.nextToken());
				return new Term(value);
			}
			if (currentToken.equals("NULL")){
				return new Term();
			}
		}
		
		System.out.println("Fail to parse the give term " + term);
		return new Term();
	}
	
	public Pair<String,String> nextMatch(String input){
		
		int startIndex = input.indexOf("(");
		if (startIndex < 0){
			System.out.println("Fail to find the next match for the give string");
			return new Pair<String,String>("ERROR!","ERROR!");			
		}else{
			int count = 1;
			for (int i = startIndex + 1; i < input.length();i++){
				if (input.charAt(i) == '(') count++;
				if (input.charAt(i) == ')') count--;
				if (count < 0){
					System.out.println("Fail to find the next match for the give string");
					return new Pair<String,String>("ERROR!","ERROR!");
				}
				if (count == 0) return new Pair<String,String>(input.substring(startIndex,i+1),input.substring(i+1));
			}
		}
		
		System.out.println("Fail to find the next match for the give string");
		return new Pair<String,String>("ERROR!","ERROR!");

	}
	
	public Formula parseFormula(String formula){
		//System.out.println(formula);
		if (formula.startsWith(" ")) return parseFormula(formula.trim());
		if (formula.startsWith("(") && formula.endsWith(")") && wellMatched(formula.substring(1,formula.length()-1))) {
			return parseFormula(formula.substring(1,formula.length()-1));
		}
		
		if (recID != null && formula.startsWith(recID)){
			Predicate tempPred = parsePredicate(formula);
			if (!setRecFormula){
				return new Formula(tempPred,new Formula());
			}else {
				ArrayList<Formula> eqList = new ArrayList<Formula>();
				for (int i = 0;i < tempPred.numArgs;i++){
					eqList.add(new Formula(recFormula.recPred.args[i],tempPred.args[i]));
				}
				
				BiAbductor bi = new BiAbductor();
				Formula recF = bi.listSubstitute(recFormula.recF, eqList);
				
				return new Formula(tempPred,recF);
			}

		}

		if (formula.equals("EMP"))
			return new Formula();
		
		if (formula.equals("TRUE"))
			return new Formula(true);
		
		if (formula.equals("FALSE"))
			return new Formula(false);
		
		if (formula.startsWith("EXT")){
			String temp = formula.substring(3);
			Term tempVar = parseTerm(nextMatch(temp).first);
			Formula tempF = parseFormula(nextMatch(temp).second);
			return new Formula(Formula.EXT,tempVar,tempF);
		}
		
		if (formula.startsWith("ALL")){
			String temp = formula.substring(3);
			Term tempVar = parseTerm(nextMatch(temp).first);
			Formula tempF = parseFormula(nextMatch(temp).second);
			return new Formula(Formula.ALL,tempVar,tempF);
		}
		
		if (formula.startsWith("NEG")){
			String temp = formula.substring(3);
			Formula tempF = parseFormula(nextMatch(temp).second);
			return new Formula(Formula.NEG,tempF);
		}
					
		
		Pair<Integer,String> foundIndex = findNextOp(formula);
		//System.out.println(foundIndex);
		if (foundIndex.first == ILLFORMED){
			System.out.println("Fail to parse the formula due to ill-formed. TERMINATE!");
			return new Formula(false);
		}
		
		if (foundIndex.first >= 0){
			String op = foundIndex.second;
			
			//Check with equality
			if (op.equals("=")){
				Term leftTerm = parseTerm(formula.substring(0,formula.indexOf("=") - 1));
				Term rightTerm = parseTerm(formula.substring(formula.indexOf("=") + 2));
				return new Formula(leftTerm,rightTerm);
			}
			
			//Check with DOT
			if (op.equals("<.>")){
				STree frac = parseTree(formula.substring(0,formula.indexOf("<.>") - 1));
				Formula dotF = parseFormula(formula.substring(formula.indexOf("<.>") + 4));
				return new Formula(frac,dotF);
			}
			
			//Check with MAP and MAP2
			if (op.startsWith("|--") && op.endsWith("-->")){
				STree frac = parseTree(op.substring(3, op.length()-3));
				Term leftTerm = parseTerm(formula.substring(0,foundIndex.first));
				String rightHS = formula.substring(foundIndex.first + 2 + op.length());
				rightHS = rightHS.substring(1,rightHS.length()-1);//Trim ( and )
				StringTokenizer tokens = new StringTokenizer(rightHS,",");

				if (tokens.countTokens() == 2) {
					Term rightTerm = parseTerm(tokens.nextToken());
					Term rightTerm2 = parseTerm(tokens.nextToken());
					return new Formula(leftTerm,rightTerm,rightTerm2,frac);
				}
				if (tokens.countTokens() == 3) {
					Term rightTerm = parseTerm(tokens.nextToken());
					Term rightTerm2 = parseTerm(tokens.nextToken());
					Term rightTerm3 = parseTerm(tokens.nextToken());
					return new Formula(leftTerm,rightTerm,rightTerm2,rightTerm3,frac);
				}
				System.out.println("Fail to parse the MAP formula!");
				return new Formula(false);
			}
			
			//Then proceed with AND,OR,STAR and IMP
			Formula leftF = parseFormula(formula.substring(0, foundIndex.first));
			Formula rightF = parseFormula(formula.substring(foundIndex.first + 2 + op.length()));
			
			if ((leftF.type == Formula.SINGLE && leftF.truth == false) || 
				(rightF.type == Formula.SINGLE && rightF.truth == false)){
				System.out.println("Fail to parse one of the sub-formula due to ill-formed. TERMINATE!");
				return new Formula(false);
			} else {
				if (op.equals("AND")){
					return new Formula(Formula.AND,leftF,rightF);
				}
				if (op.equals("OR")){
					return new Formula(Formula.OR,leftF,rightF);
				}
				if (op.equals("*")){
					return new Formula(Formula.STAR,leftF,rightF);
				}
				if (op.equals("IMP")){
					return new Formula(Formula.IMP,leftF,rightF);
				}
			}
		}
		
		if (foundIndex.first == NOTFOUND){
			
			if (formula.indexOf("=") >= 0){
				Term leftTerm = parseTerm(formula.substring(0,formula.indexOf("=") - 1));
				Term rightTerm = parseTerm(formula.substring(formula.indexOf("=") + 2));
				return new Formula(leftTerm,rightTerm);
			}
			
		}
		
		return new Formula(false);
	}
	
	public Predicate parsePredicate(String predicate){
		
		String predicateID = predicate.substring(0,predicate.indexOf("("));
		String arguments = predicate.substring(predicate.indexOf("(")+1,predicate.length()-1);
		StringTokenizer tokens = new StringTokenizer(arguments,",");
		int numArgs = tokens.countTokens();
		Term[] args = new Term[numArgs];
		
		for (int i = 0;i < numArgs;i++){
			args[i] = parseTerm(tokens.nextToken());
		}
		
		return new Predicate(predicateID,numArgs,args);
	}
	
	
	//Parse the recursive formula, also set setRecFormula to true
	//String is supposed to have the form 
	//recname(arg1,...,argn):=recformula
	public Formula parseRec(String formula){
		
		int splitIndex = formula.indexOf(":=");
		String left = formula.substring(0, splitIndex);
		String right = formula.substring(splitIndex + 2);
		
		Predicate recPred = parsePredicate(left);
		recID = recPred.id;
		Formula recF = parseFormula(right);
		
		Formula result = new Formula(recPred,recF);
		recFormula = result.cloneFormula();
		setRecFormula = true;
		
		return result;
	}
	
	public boolean wellMatched(String formula) {
		int bracketCount = 0;
		for (int i = 0; i < formula.length();i++) {
			if (formula.charAt(i) == '(') bracketCount++;
			if (formula.charAt(i) == ')') {
				bracketCount--;
				if (bracketCount < 0) return false;
			}
		}
		
		return bracketCount == 0;
	}
}

//Term construction for formulas
public class Term {
	
	//Term := int | NULL | var
	
	//Constant declaration
	public static final int NULL = 1;
	public static final int VALUE = 2;
	public static final int VAR = 3;
	
	//Internal data declaration
	public int val;
	public String var;
	public int type;
	
	//List of constructors for Term
	public Term(){
		
		this.type = NULL;
	}
		
	public Term(int val){
		
		this.type = VALUE;
		this.val = val;
	}
	
	public Term(String var){
		
		this.type = VAR;
		this.var = var;
	}
	
	//Method to print out the term
	public String toString(){
		if(type == NULL) return "NULL";
		if(type == VALUE) return "VAL " + val;
		if(type == VAR) return "VAR " + var;
		
		System.out.println("Error in the method Term.toString()!");
		return "";
	}
	
	//Method to copy a term
	public Term cloneTerm(){
		if(type == NULL) return new Term();
		if(type == VALUE) return new Term(val);
		if(type == VAR) return new Term(var);
		
		System.out.println("Error in the method Term.cloneTerm()!");
		return new Term();
	}
	
	public boolean equals(Term t){
		
		if (type == t.type){
			if (type == NULL) return true;
			if (type == VALUE) return (val == t.val);
			if (type == VAR) return (var.equals(t.var));
		}
		
		return false;
	}
}

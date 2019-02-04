import java.util.Arrays;

public class Predicate {
	
	//Internal data structure
	public String id;
	public int numArgs;
	public Term[] args;
	
	public Predicate(){
		this.id = "UNKNOWN";
		this.numArgs = 0;
		this.args = new Term[0];
	}
	
	public Predicate(String id){
		this.id = id;
		this.numArgs = 0;
		this.args = new Term[0];
	}
	
	public Predicate(String id,int numArgs,Term[] args){
		if (args.length != numArgs){
			System.out.println("Error in the constructor of Predicate!");
		}else{
			this.id = id;
			this.numArgs = numArgs;
			this.args = Arrays.copyOf(args,args.length);
		}
	}
	
	public boolean equals(Predicate p){
		if (id.equals(p.id) && numArgs == p.numArgs){
			for (int i = 0;i < numArgs;i++){
				if (!args[i].equals(p.args[i])) return false;
			}
			return true;
		}
			
		return false;
	}
	
	public String toString(){
		
		String result = id;
		if (numArgs == 0) return result;
		
		result = result + "(" + args[0];
		for (int i = 1; i < args.length; i++){
			result = result + "," + args[i];
		}
		result = result + ")";
		
		return result;
	}
	
	public Predicate clonePredicate(){
		return new Predicate(id,numArgs,args);
	}

}

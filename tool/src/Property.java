//This class is used to define properties such as uniformity, precise, precisely, etc.
public class Property {
	
	//Constant declaration
	public static final int UNIFORM = 1;
	public static final int PRECISELY = 2;
	
	//Internal data structure declaration
	public int type;
	public STree tree;
	public Formula f;
	
	public Property(Formula f){
		this.type = PRECISELY;
		this.f = f.cloneFormula();
	}
	
	public Property(STree tree){
		this.type = UNIFORM;
		this.tree = tree.cloneTree();
	}
	
	public Property cloneProperty(){
		if (type == PRECISELY)
			return new Property(f.cloneFormula());
		if (type == UNIFORM)
			return new Property(tree);
		
		System.out.println("Error in the method Property.cloneProperty()!");
		return null;
	}
	
	public String toString(){
		if (type == PRECISELY) return "PRECISELY (" + f + ")";
		if (type == UNIFORM) return "UNIFORM (" + tree + ")";
		
		return "Error in the method Property.toString()!";
	}
}

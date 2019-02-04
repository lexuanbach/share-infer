//Tree shares and their basic operations
public class STree {
	
	//Constant declaration
	public static final boolean BLACK = true;
	public static final boolean WHITE = false;
	public static final int LEAF = 1;
	public static final int TREE = 2;
	public static final int ERROR = -1;
	
	//Internal data declaration
	public int type;
	public boolean leaf;
	public STree leftTree, rightTree;
	
	//Constructor for error
	public STree() {
		this.type = ERROR;
	}
	
	//Constructor for leaf
	public STree(boolean leaf){
		this.leaf = leaf;
		this.type = LEAF;
	}
	
	//Constructor for tree
	public STree(STree left, STree right){
		this.leftTree = left.cloneTree();
		this.rightTree = right.cloneTree();
		this.type = TREE;
	}
	
	//Clone a new tree
	public STree cloneTree(){
		if (type == LEAF) return new STree(leaf);
		
		if (type == TREE){
			STree leftTemp = leftTree.cloneTree();
			STree rightTemp = rightTree.cloneTree();
			return new STree(leftTemp,rightTemp);
		}
		
		System.out.println("Error in method STree.cloneTree()!");
		return new STree(BLACK);
	}
	
	//Check whether the given tree is in canonical form
	public boolean isCanon(){
		// Base case
		if(type == LEAF)  return true;
		
		//Inductive case
		if(type == TREE){
			// Case [B B] and [W W]
			if (leftTree.type == LEAF && rightTree.type == LEAF){
				if (leftTree.leaf == BLACK && rightTree.leaf == BLACK) return false;
				if (leftTree.leaf == WHITE && rightTree.leaf == WHITE) return false;
			}
			//Recursive call to left and right subtrees
			return leftTree.isCanon() && rightTree.isCanon();
		}
		
		System.out.println("Error in method STree.isCanon()!");
		return false;
	}
	
	//Turn an arbitrary boolean binary tree into canonical form
	public STree makeCanon(){
		//Base case
		if(type == LEAF) return new STree(leaf);
		
		//Inductive case
		if(type == TREE){
			// Case [B B] and [W W]
			if (leftTree.type == LEAF && rightTree.type == LEAF){
				if (leftTree.leaf == BLACK && rightTree.leaf == BLACK) return new STree(BLACK);
				if (leftTree.leaf == WHITE && rightTree.leaf == WHITE) return new STree(WHITE);
				return new STree(leftTree.cloneTree(),rightTree.cloneTree());
			}

			if (leftTree.type == TREE && rightTree.type == LEAF){
				STree leftTemp = leftTree.makeCanon();
				
				if (leftTemp.type == LEAF && leftTemp.leaf == BLACK && rightTree.leaf == BLACK) return new STree(BLACK);
				if (leftTemp.type == LEAF && leftTemp.leaf == WHITE && rightTree.leaf == WHITE) return new STree(WHITE);

				return new STree(leftTemp,rightTree.cloneTree());
			}
			
			if (leftTree.type == LEAF && rightTree.type == TREE){
				STree rightTemp = rightTree.makeCanon();
				
				if (rightTemp.type == LEAF && leftTree.leaf == BLACK && rightTemp.leaf == BLACK) return new STree(BLACK);
				if (rightTemp.type == LEAF && leftTree.leaf == WHITE && rightTemp.leaf == WHITE) return new STree(WHITE);
				
				return new STree(leftTree.cloneTree(),rightTemp);
			}
			
			if (leftTree.type == TREE && rightTree.type == TREE){
				STree leftTemp = leftTree.makeCanon();
				STree rightTemp = rightTree.makeCanon();
					
				if (leftTemp.type == LEAF && rightTemp.type == LEAF){
					if (leftTemp.leaf == BLACK && rightTemp.leaf == BLACK) return new STree(BLACK);
					if (leftTemp.leaf == WHITE && rightTemp.leaf == WHITE) return new STree(WHITE);
				} 
				
				return new STree(leftTemp,rightTemp);
			}		
		}
		
		System.out.println("Error in method STree.makeCanon()!");
		return new STree();
	}
	
	//Method to print out the string representation of the tree
	public String toString(){
		
		if(type == LEAF){
			if(leaf == BLACK) return "B";
			if(leaf == WHITE) return "W";
		}
		
		if(type == TREE){
			return "[ " + leftTree.toString() + " " + rightTree.toString() + " ]";
		}

		return "Error in method STree.toString()!";
	}
	
	//Method to union two trees, the result tree needs not to be canonical
	public STree treeUnion(STree t){
		
		if(type == LEAF){
			if (leaf == BLACK) return new STree(BLACK);
			if (leaf == WHITE) return t.cloneTree();
		}
		
		if(t.type == LEAF){
			if (t.leaf == BLACK) return new STree(BLACK);
			if (t.leaf == WHITE) return cloneTree();
		}
		
		if(type == TREE && t.type == TREE){
			STree leftTemp = leftTree.treeUnion(t.leftTree);
			STree rightTemp = rightTree.treeUnion(t.rightTree);
			return new STree(leftTemp,rightTemp);
		}
		
		System.out.println("Error in the method STree.treeUnion()!");
		return new STree();
	}
	
	//Method to intersect two trees, the result tree needs not to be canonical
	public STree treeIntersect(STree t){
		
		if(type == LEAF){
			if (leaf == WHITE) return new STree(WHITE);
			if (leaf == BLACK) return t.cloneTree();
		}
		
		if(t.type == LEAF){
			if (t.leaf == WHITE) return new STree(WHITE);
			if (t.leaf == BLACK) return cloneTree();
		}
		
		if(type == TREE && t.type == TREE){
			STree leftTemp = leftTree.treeIntersect(t.leftTree);
			STree rightTemp = rightTree.treeIntersect(t.rightTree);
			return new STree(leftTemp,rightTemp);
		}
		
		System.out.println("Error in the method STree.treeIntersect()!");
		return new STree();
	}
	
	//Method to complement a tree
	public STree treeComp(){
		
		if(type == LEAF){
			if (leaf == WHITE) return new STree(BLACK);
			if (leaf == BLACK) return new STree(WHITE);
		}
		
		if(type == TREE){
			STree leftTemp = leftTree.treeComp();
			STree rightTemp = rightTree.treeComp();
			return new STree(leftTemp,rightTemp);
		}
		
		System.out.println("Error in the method STree.treeComp()");
		return new STree();
	}	
	
	//Check whether the current tree is joinable with t
	public boolean joinable(STree t) {
		
		STree temp = treeIntersect(t);
		temp = temp.makeCanon();
		
		if (temp.type == LEAF && temp.leaf == WHITE) return true;
		return false;
	}
	
	//Join the current tree with t, 
	//with assumption that joinable(t) returns true
	//and the result tree is reduced to canonical form
	public STree join(STree t) {
		
		if(!joinable(t)) {
			System.out.println("Not joinable!");
			return new STree();
		}
		
		
		STree temp = treeUnion(t);
		temp = temp.makeCanon();
		return temp;
	}
	
	//Return this tree - t
	public STree substract(STree t){
		STree result = t.treeComp();
		result = treeIntersect(result);
		result = result.makeCanon();
		
		return result;
	}
	
	//Return Yes iff this tree intersect t = this tree
	public boolean isSub(STree t){
		STree result = treeIntersect(t);
		result = result.makeCanon();
		return result.equals(makeCanon());
	}
	
	//Return this tree bowtie t
	public STree treeMul(STree t){
		
		if (type == LEAF){
			if (leaf == BLACK) {
				return t.makeCanon().cloneTree();
			}
			if (leaf == WHITE) {
				return new STree(WHITE);
			}
		}
		
		if (type == TREE){
			STree tempTree = new STree(leftTree.treeMul(t),rightTree.treeMul(t));
			tempTree = tempTree.makeCanon();
			return (tempTree.makeCanon()).cloneTree();
		}
		
		return new STree();
	}
	
	//Check whether two trees are equal
	public boolean equals(STree t) {

		if(type != t.type) return false;
		
		if(type == LEAF && t.type == LEAF) {
			if(leaf == t.leaf) return true;
			else return false;
		}
		
		if(type == TREE && t.type == TREE) {
			return leftTree.equals(t.leftTree) && rightTree.equals(t.rightTree);
		}
		
		return false;
	}
}

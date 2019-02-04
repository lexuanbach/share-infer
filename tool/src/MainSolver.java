import java.io.*;
import java.util.*;

public class MainSolver {
	
	public static final String exampleDir = "examples/";
	
	public MainSolver(){}
	
	public String readAndSolve(String inputFile){
		
		try(BufferedReader reader = new BufferedReader(new FileReader(new File(inputFile)))) {
			FormulaParser fParser = new FormulaParser();
		    String line = reader.readLine().trim();

		    if (line.startsWith("UNIFORM")){
		    	
		    	STree uTree = new STree();
		    	
		    	//Remove UNIFORM from line
		    	line = line.substring(7).trim();
		    	//Check whether it contains a specific tree after that
		    	if (!line.equals("")){
		    		uTree = fParser.parseTree(line);
		    	}
		    	//Read the second line
		    	line = reader.readLine().trim();
		    	//If the second line is the definition of the recursive predicate
		    	if (line.startsWith("REC")){
		    		//Remove REC from line
		    		line = line.substring(3).trim();
		    		//Read the recursive predicate
		    		fParser.parseRec(line);
		    		//Move to the next line
		    		line = reader.readLine().trim();
		    	}
		    	
		    	Formula formula = fParser.parseFormula(line);
		    	//System.out.println(line);
		    	UniChecker uChecker = new UniChecker();

		    	//If there is no tree provided in the first line, try to guess one
		    	if (uTree.type == STree.ERROR){
			    	Pair<Integer,STree> result = uChecker.findUniform(formula);
			    	uChecker.reset();
			    	if (result.first == UniChecker.YES){
			    		return "YES " + result.second; 
			    	} else if (result.first == UniChecker.ANY){
			    		return "ANY";
			    	} else if (result.first == UniChecker.NO) {
			    		return "NO";
			    	} else {
			    		return "UNKNOWN";
			    	}
		    	} else{
		    		int result = uChecker.checkUniform(formula, uTree);
		    		uChecker.reset();
			    	if (result == UniChecker.YES || result == UniChecker.ANY){
			    		return "YES " + uTree; 
			    	} else {
			    		return "NO";
			    	}
		    	}
		    }
		    
		    if (line.startsWith("PRECISE")){
		    	
		    	//Read the second line
		    	line = reader.readLine().trim();
		    	//If the second line is the definition of the recursive predicate
		    	// then parse it using the parser
		    	if (line.startsWith("REC")){
		    		//Remove REC from line
		    		line = line.substring(3).trim();
		    		//Read the recursive predicate
		    		fParser.parseRec(line);
		    		//Move to the next line
		    		line = reader.readLine().trim();
		    	}
		    	
		    	PreciseChecker pChecker = new PreciseChecker();
		    	Formula formula = fParser.parseFormula(line);
		    	int result = pChecker.checkPrecisely(formula);
		    	pChecker.reset();
		    	if (result == PreciseChecker.YES){
		    		return "YES";
		    	} else if (result == PreciseChecker.NO){
		    		return "NO";
		    	} else {
		    		return "UNKNOWN";
		    	}
		    }
		    
		    if (line.startsWith("BIABDUCTION")){
		    	
		    	//Read the second line
		    	line = reader.readLine().trim();
		    	//If the second line is the definition of the recursive predicate
		    	// then parse it using the parser
		    	if (line.startsWith("REC")){
		    		//Remove REC from line
		    		line = line.substring(3).trim();
		    		//Read the recursive predicate
		    		fParser.parseRec(line);
		    		//Move to the next line
		    		line = reader.readLine().trim();
		    	}
		    	//Read the antecedent
		    	Formula anteF = fParser.parseFormula(line);
		    	
		    	line = reader.readLine().trim();
		    	//Read the consequent
		    	Formula conF = fParser.parseFormula(line);
		    	
		    	BiAbductor biAb = new BiAbductor();
		    	Pair<Formula,Formula> result = biAb.biAbduct(anteF,conF);
		    	return result.first + "\n" + result.second;
		    }
		    
		    reader.close();
		    
		} catch(IOException e){
			System.out.println("Fail to read the file " + inputFile);
			System.out.println("Error detail: " );
			e.printStackTrace();
		}
		
		return "ERROR!";
	}
	//After solving the problem, write the result to outputFile
	//The last line is the computation time in seconds
	public void readSolveAndWrite(String inputFile,String outputFile){
		long startTime = System.nanoTime();
		String result = readAndSolve(inputFile);
		long stopTime = System.nanoTime();
		double time = Math.round((stopTime - startTime)/100000.0)/10000.0;
		System.out.println();
		System.out.println("Time taken: " + time + " seconds");
		
		PrintWriter writer;
		try {
			writer = new PrintWriter(outputFile, "UTF-8");
			writer.println(result);
			writer.print(time);
			writer.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args){
		
		MainSolver solver = new MainSolver();
		
		if (args.length == 1 && args[0].equals("-demo")){
			System.out.println("Opening the directory " + exampleDir);
			File folder = new File(exampleDir);
			File[] fileList = folder.listFiles();
			for (int i = 0 ; i < fileList.length;i++){
				System.out.println("Reading file " + fileList[i].getName());
				if(!fileList[i].getName().startsWith("result")){
					solver.readSolveAndWrite(exampleDir + fileList[i].getName(),exampleDir + "result_" + fileList[i].getName());
					System.out.println("\n+++++++++++++++++++++++\n");					
				}
			}
		} else if (args.length != 2){
			System.out.println("Wrong number of arguments. Either try with -demo or inputFile outputFile");
		} else {
			solver.readSolveAndWrite(exampleDir + args[0],exampleDir + args[1]);
		}
	}
}

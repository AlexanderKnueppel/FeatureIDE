/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.featurehouse.proofautomation.builder;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableSet;

import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;

/**
 * 
 * Contains the methods which works on the metaproduct to adapte the code for key
 * 	//requires_update_dailylimit=FM.FeatureModel.dailylimit  &&  x != 0;
	
  	/*@ public normal_behaviour
	@ requires \dl_OriginalPre && \disjoint(withdraw, \dl_OriginalFrame);
	@ ensures \dl_OriginalPost;
	@ ensures \result ==> (((x < 0) ==> (\old(withdraw) + x >= DAILY_LIMIT)) && \old(update_BankAccount(x)));
	@ ensures (((x < 0) && (\old(withdraw) + x < DAILY_LIMIT)) || !\old(update_BankAccount(x))) ==> !\result;
	@ assignable \dl_OriginalFrame, withdraw;
	
	boolean update_DailyLimit(int x) {
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw += x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		if (!update_BankAccount(x))
			return false;
		withdraw = newWithdraw;
		return true;
	}
 * @author Stefanie
 */
public class MetaProductBuilderNonRigid {
	
	public static String FILE_SEPERATOR = System.getProperty("file.separator");
	/**
	 * Prepares the metaproduct for verification
	 * @param metaproductLocation src folder which contains the metaproduct
	 */
	public static void prepareMetaProduct(File metaproductLocation){
		File account = new File(metaproductLocation.getAbsolutePath()+FILE_SEPERATOR+"Account.java");
		BuilderUtil.removeBracketsOfVar(account, "lock");
		BuilderUtil.removeBracketsOfVar(account, "result");
		BuilderUtil.fixUpdateLoggingInBA5BA6(account);
	}

	public static void main(String[] args) {
		File proof = new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/Sandbox/Evaluation/2021-01-04 13-32-35/1 Fefalution + Family Proof Replay/BankAccountv1/Partial Proofs for Metaproduct/InterestEstimation/"+
	"Account(Account__calculateInterest()).JML normal_behavior operation contract.0.proof");
		File projectDir = new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/SandBox/BankAccountv1/");
		File f = new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/Sandbox/Evaluation/2021-01-04 13-32-35/1 Fefalution + Family Proof Replay/BankAccountv1/");
		//preparePartialProofs(projectDir,f);
		Map<String, String> contractsMap = getContract(proof);
		if(contractsMap != null) {
			prepareContracts(contractsMap);
		}
		//File ba2stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv2"+FILE_SEPERATOR+featureStubDir);
		//List<File> featurestubs = getAllPartialProofs(projectDir,evalPath);
		/*
		String methodname = getMethodName(proof);
		String method_to_replace = methodname + "_original_" + f.getName();
		
		System.out.println("method name : " + methodname);
		System.out.println("method to replace : " + method_to_replace);
		
		System.out.println("Classname : " + getClassName(proof)+".java");
		
		File metaproduct = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\2019-1127 09-53-48\\VA1 (EVEFI)\\BankAccountv1\\"+FileManager.metaproductDir + "\\"+getClassName(proof)+".java");
		
		if(checkForOriginal(proof,f.getName())){
			System.out.println("Original found! Original method name is " + getOriginalMethod(methodname,f.getName(),metaproduct));
			System.out.println("The original method " + getOriginalMethod(methodname,f.getName(),metaproduct));
			System.out.println("Possible replacement " + "dispatch_" + methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct));
			System.out.println("Does replacement exist? -> " + (checkForMethod("dispatch_" + methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct),metaproduct) ? "Yes" : "No"));
			
			if(!checkForMethod("dispatch_" + methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct),metaproduct)) {
				String replace_with = methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct);
				System.out.println("This is the alternative: " + replace_with);
			}
		}*/
	}
	
	private static void prepareContracts(Map<String, String> contractsMap) {
		String[] variableString = new String[1];
		if(contractsMap.containsKey("assignable")) {
			String assignable = contractsMap.get("assignable").replace(";", "");
			String[] variables = assignable.split(",");
			assignable = "";
			int i =0;
			variableString = new String[variables.length];
			for(String var : variables) {
				if(!var.contains("\nothing")) {
					variableString[i++] = var.trim();
					var = "self." + var.trim();					
				}
				assignable = assignable +var + ", ";
			}
			assignable  = assignable.substring(0,assignable.length()-2);
			System.out.println(assignable);
		}
		if(contractsMap.containsKey("requires")) {			
			String require = contractsMap.get("requires").replace(";", "");
			for(String var: variableString) {
				if(require.contains("\\old("+var+")")) {
					require = require.replace("\\old("+var+")", "self."+var);
					System.out.println(require);
				}
			}

			require = require.replace("x ", "_x ");
			require = require.replace(" || ", " |");
			require = require.replace(" && ", " &");
			require = require.replace("(\\result)", "result = true");
			
		}
		if(contractsMap.containsKey("ensures")) {
			String ensures = contractsMap.get("ensures").replace(";", "");
			for(String var: variableString) {
				if(ensures.contains("\\old("+var+")")) {
					ensures = ensures.replace("\\old("+var+")", "self."+var+"@heapAtPre");
					System.out.println(ensures);
				}
			}
			ensures = ensures.replace("x ", "_x ");
			ensures = ensures.replace(" || ", " |");
			ensures = ensures.replace(" && ", " &");
			ensures = ensures.replace("(\\result)", "result = true");
			System.out.println(ensures);
		}
	}
	
	private static Map<String, String> getContract(File reuseProof) {
		String proofPath = reuseProof.getParentFile().getParentFile().getParentFile().getAbsolutePath()+FILE_SEPERATOR+"src";
		String[] tmpString = reuseProof.getName().split("\\(");
		String featureName = tmpString[0];
		String methodName = tmpString[1].substring(tmpString[1].lastIndexOf("__")+2);

		try {
			BufferedReader bReader = new BufferedReader(new FileReader(proofPath+FILE_SEPERATOR+featureName+".java"));
            String line = bReader.readLine();
            Map<String, String> contractsMap = new HashMap<>();
            while(line != null) {
            	System.out.println(line);
            	if(line.contains("/*@") && !line.contains("/*@pure@*/")){
            		while(!line.contains("@*/")) {            			 
            			 String tmp = line.split(" ")[0];
            			 if(tmp.equals("requires")) {            				 
            				 line = line.replace(tmp, "").trim();
            				 contractsMap.put("requires", line);
            			 }
            			 if(tmp.equals("ensures")) {
            				 contractsMap.put("ensures", line.replace(tmp, ""));
            			 }
            			 if(tmp.equals("assignable")) {
            				 contractsMap.put("assignable", line.replace(tmp, ""));
            			 }
            			 line = bReader.readLine().trim();
            		}
            		line = bReader.readLine().trim();
            	}
            	if(line.contains(methodName+"_BankAccount(") && line.endsWith("{")) {
                 	return contractsMap;
            	}else {
            		contractsMap.clear();
            	}            	
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
		return null;
	}
	
	/**
	 * Performs the proof transformation for all partial proofs if necessary
	 * @param projectDir Directory of the Project contains Directory "Partial Proofs for Metaproduct" with proofs of the featurestub
	 */
	public static void preparePartialProofs(File projectDir, File evalPath){
		File partialProofs = new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir);
		System.out.println("Prepare " + partialProofs + " for Partialproofs");
		File[] featurestubs = partialProofs.listFiles();
		for(File f : featurestubs){
			if(f.isDirectory()){
				File[] proofs = f.listFiles();
				for(File proofFile: proofs){
					if(proofFile.getName().endsWith(".proof")) {
						
						
						String methodname = getMethodName(proofFile);//undoUpdate
						String method_to_replace = methodname + "_original_" + f.getName();

						//
						replaceJavaSource(proofFile);
						File metaproduct = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir+FILE_SEPERATOR+getClassName(proofFile)+".java");
						if(checkForOriginal(proofFile,f.getName())){
							String replace_with = "dispatch_" + methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct);
							if(!checkForMethod(replace_with,metaproduct)) {
								replace_with = methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct);
							}
							//replaceMethodNamesInPartialProofs(method_to_replace,replace_with,f.getName(),proofFile);
							//renameAbstractKeywords(proofFile, f, methodname);
							//renameRemainingStuff(proofFile, f, methodname);
							renameProof(proofFile,f,methodname+"_"+f.getName());

						}
						else{
							String extensionForBankAccount = "";
							List<String> whitelist = new ArrayList<String>();
							whitelist.add("update");
							whitelist.add("undoUpdate");
							whitelist.add("nextDay");
							whitelist.add("nextYear");
							if(whitelist.contains(methodname) && f.getName().equals("BankAccount")) {
								extensionForBankAccount += "_BankAccount";
							}
							//renameAbstractKeywords(proofFile, f, methodname);
						//	renameRemainingStuff(proofFile, f, methodname);
							renameProof(proofFile,f,methodname+extensionForBankAccount);
							
						}
						
					
					}
					if(proofFile.getName().endsWith(".key")) {
						removeUnderscoresStuff(proofFile);
					}
					
					//replaceMethodNamesInPartialProofs(methodname,methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct),f.getName(),proof);
					//renameProof(proof,f,methodname+"_"+f.getName());
				}
			}
		}
	}
	
	/**
	 * Removes underscores in KeY-file
	 * @param proof
	 */
	private static void removeUnderscoresStuff(File proof){
		StringBuffer sbuffer = new StringBuffer();
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(proof));
            String line = bReader.readLine();
            while(line != null) {
            	if(line.contains("_")){
            		line = line.replaceAll("_", "");
            	} 
            	sbuffer.append(line + System.getProperty("line.separator"));
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,proof);
	}
	
	/**
	 * replaces the javasource in the proof-File with ../../../../../../src
	 * and add Non rigid functions
	 * otherwise it won't find the correct folder 
	 * @param proof
	 */
	private static void replaceJavaSource(File proof){
		StringBuffer sbuffer = new StringBuffer();
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(proof));
            String line = bReader.readLine();
            String folderString = proof.getParentFile().getParentFile().getParentFile().getName();
            while(line != null) {
            	if(line.startsWith("\\javaSource")) {
            		//line = "\\javaSource \".."+FILE_SEPERATOR+".."+FILE_SEPERATOR+".."+FILE_SEPERATOR+".."+FILE_SEPERATOR+".."+FILE_SEPERATOR+".."+FILE_SEPERATOR+folderString+FILE_SEPERATOR+"src\";"+

            		//line = "\\javaSource \".."+FILE_SEPERATOR+".."+FILE_SEPERATOR+"src\";"+
            		line = line + 
            				"\n\n"+ "\\functions {\n" + 
            				"  LocSet OriginalFrame;\n" + 
            				"}\n" + 
            				"\n" + 
            				"\\predicates {\n" + 
            				"  \\nonRigid OriginalPre;\n" + 
            				"  \\nonRigid OriginalPost;\n" + 
            				"}";
            	}
            	sbuffer.append(line + System.getProperty("line.separator"));
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,proof);
	}
	
	/**
	 * 
	 * @param proof
	 * @param stub
	 * @param methodname
	 */
	private static void renameRemainingStuff(File proof, File stub, String methodname){
		StringBuffer sbuffer = new StringBuffer();
		String newmethodname = methodname + "_" + stub.getName();
		//String newmethodname = methodname ;
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(proof));
            String line = bReader.readLine();
            while(line != null) {
            	if(line.startsWith("name=")){
            		line = line.replaceAll(methodname, newmethodname);
            	} 
            	
            	if(line.startsWith("contract=")){
            		line = line.replaceAll(methodname, newmethodname);
            	} 
            	
            	if(line.contains("methodBodyExpand")){
            		line = line.replaceAll(methodname, newmethodname);
            	}
            	sbuffer.append(line + System.getProperty("line.separator"));
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,proof);
	}
	/**
	 * 
	 * @param proof
	 * @param stub
	 * @param methodname
	 */
	private static void renameAbstractKeywords(File proof, File stub, String methodname){
		StringBuffer sbuffer = new StringBuffer();
		String newmethodname = methodname + "_" + stub.getName();
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(proof));
            String line = bReader.readLine();
            while(line != null) {
            	if(line.contains(methodname + "E")){
            		line = line.replaceAll(methodname + "E", newmethodname + "E");
            	} else if(line.contains(methodname + "R")) {
            		line = line.replaceAll(methodname + "R", newmethodname + "R");
          	} else if(line.contains(methodname + "A")) {
            		line = line.replaceAll(methodname + "A", newmethodname + "A");
            	}
            	sbuffer.append(line + System.getProperty("line.separator"));
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,proof);
	}
	
	/**
	 * Renames the featurestub proofs to classname_methodname with the methodname of the metaproduct
	 * @param proof
	 * @param featurestub
	 * @param methodname
	 */
	private static void renameProof(File proof, File featurestub, String methodname){
		File newName = new File(featurestub.getAbsolutePath()+FILE_SEPERATOR+getClassName(proof)+"_"+methodname+".proof");
		proof.renameTo(newName);
	}
	
	/**
	 * Returns true if the given file contains an original call with methodname_original_featurestub
	 * @param f
	 * @param featurestub
	 * @return
	 */
	public static boolean checkForOriginal(File f, String featurestub){
		if(f.getAbsolutePath().endsWith(".proof")&&!f.getAbsolutePath().contains("inv")){
			try {
				BufferedReader bReader = new BufferedReader(new FileReader(f));
	            String line = bReader.readLine();
	            String methodname = getMethodName(f);
	            while(line != null) {
	            	
	            	if(line.contains(methodname+"_original_"+featurestub)){
	            		bReader.close();
	            		return true;
	            	}
	            	line = bReader.readLine();
	            }
	            bReader.close();
	        } catch(IOException e) {
	            return false;
	        }
		}
		return false;
	}
	
	/**
	 * 
	 * @param method
	 * @param metaproductClass
	 * @return true if the given file contains the given method
	 */
	public static boolean checkForMethod(String method, File metaproductClass){
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(metaproductClass));
            String line = bReader.readLine();
            while(line != null) {           	
            	if(line.matches(".*"+method+"\\s*\\(.*\\)\\s*\\{.*")){
            		bReader.close();
            		return true;
            	}
            	line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            return false;
        }
		return false;
	}
	
	/**
	 * Returns the proven method name of the File
	 * @param f
	 * @return
	 */
	private static String getMethodName(File f){
		
		String filename = f.getName();
		
		String[] filenameParts = filename.split("\\.");
		if(filenameParts[0].contains("java")){
			System.out.println(filenameParts[0]);
			return "inv";
		}
		else{
			String[] nameParts = filenameParts[0].split("__");
			return nameParts[1].replaceAll("\\(.*\\)", "");
		}
	}
	
	/**
	 * Returns the class of the proven method in file f
	 * @param f
	 * @return
	 */
	private static String getClassName(File f){
		String filename = f.getName();
		String[] filenameParts = filename.split("\\(");
		return filenameParts[0];
	}
	
	/**
	 * Returns featurestub e.g. DailyLimit of orginial() call
	 * @param methodname
	 * @param featurestub
	 * @param metaproduct
	 * @return
	 */
	private static String getOriginalMethod(String methodname, String featurestub, File metaproduct){
		try{
			BufferedReader bReader = new BufferedReader(new FileReader(metaproduct));
			String line = bReader.readLine();
			boolean curMethod = false;
			while(line != null){
				if(curMethod){
					if(line.contains(methodname+"_")){
						String[] nameParts = line.split(methodname+"\\_");
						String[] original = nameParts[1].split("\\(");
						bReader.close();
						return original[0];
					}
				}
				if(line.matches(".*"+methodname+"_"+featurestub+"\\s*\\(.*\\)\\s*\\{.*")){
					curMethod = true;
				}
				line = bReader.readLine();
			}
			bReader.close();
		}
		catch(IOException e) {
			e.printStackTrace();
		}
		return "";
	}
	
	/**
	 * Replaces methodnames of featurestubs to methodnames of the metaproduct
	 * @param oldName
	 * @param newName
	 * @param featurestub
	 * @param proof
	 */
	private static void replaceMethodNamesInPartialProofs(String oldName, String newName
			,String featurestub, File proof){
		System.out.println("Replace " + oldName + " in  " + getMethodName(proof)+ "_"+featurestub  + " with " + newName);
		StringBuffer sbuffer = new StringBuffer();
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(proof));
            String line = bReader.readLine();
            while(line != null) {
            	if(line.contains(oldName)){
            		line = line.replaceAll(oldName, newName);
            	}
            	sbuffer.append(line + System.getProperty("line.separator"));
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,proof);
	}
	
	private static Map<String, String> getOriginalContract(File proofFile, File evalPath) {
		String nameString = proofFile.getParentFile().getName();
		String[] tmpString = proofFile.getName().split("\\(");
		String featureName = tmpString[0];
		String methodName = tmpString[1].substring(tmpString[1].lastIndexOf("__")+2);
		String featurePath = evalPath.getAbsoluteFile() + FILE_SEPERATOR + FileManager.metaproductDir+FILE_SEPERATOR + featureName+".java";
		BufferedReader bReader;
		Map<String, String> contractMap = new HashMap<String, String>();
		try {
			bReader = new BufferedReader(new FileReader(featurePath));
			String line = bReader.readLine();
	        while(line != null) {
	        	
	        	if(line.contains(methodName+"_"+nameString+"R = ")) {
	        		String[] subStrings = line.split(" = ");
	        		System.out.println( subStrings[1]);
	        		contractMap.put("R", subStrings[1]);
	        	}
	        	line = bReader.readLine();
	        }
		} catch (IOException e) {
			e.printStackTrace();
		}
		return contractMap;
	}

}

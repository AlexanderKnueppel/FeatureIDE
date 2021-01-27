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
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.collections4.bag.SynchronizedSortedBag;
import org.junit.Ignore;
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
		//File proof = new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/Sandbox/Evaluation/2021-01-04 13-32-35/1 Fefalution + Family Proof Replay/BankAccountv1/Partial Proofs for Metaproduct/InterestEstimation/"+
	//"Account(Account__calculateInterest()).JML normal_behavior operation contract.0.proof");
		//File projectDir = new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/SandBox/BankAccountv1/");
		//File f = new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/Sandbox/Evaluation/2021-01-04 13-32-35/1 Fefalution + Family Proof Replay/BankAccountv1/");
		//preparePartialProofs(projectDir,f);

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
		File f = new File("F:\\Homeoffice\\Abschlussarbeiten\\Fefalution\\attempt\\BankAccountv1\\src\\Transaction.java");
		File evalPath = new File("F:\\Homeoffice\\Abschlussarbeiten\\Fefalution\\\\attempt\\BankAccountv1\\");
		//File ba2stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv2"+FILE_SEPERATOR+featureStubDir);
		//List<File> featurestubs = getAllPartialProofs(projectDir,evalPath);
		
		//System.out.println(getOriginalMethod("update", "DailyLimit", f));

//		enhanceContractWithPredicateDetails("Account",f, evalPath, "BankAccount", "", "");
////		//enhanceContractWithPredicateDetails("update_BankAccount",f, evalPath, "BankAccount", "", "");
//		enhanceContractWithPredicateDetails("update",f, evalPath, "BankAccount", "", "");
//		enhanceContractWithPredicateDetails("update",f, evalPath, "DailyLimit", "", "");
//		enhanceContractWithPredicateDetails("undoUpdate",f, evalPath, "BankAccount", "", "");
//		enhanceContractWithPredicateDetails("undoUpdate",f, evalPath, "DailyLimit", "", "");
//		enhanceContractWithPredicateDetails("calculateInterest",f, evalPath, "Interest", "", "");
//		enhanceContractWithPredicateDetails("estimatedInterest",f, evalPath, "InterestEstimation", "", "");
//		enhanceContractWithPredicateDetails("credit",f, evalPath, "CreditWorthiness", "", "");
//		enhanceContractWithPredicateDetails("lock",f, evalPath, "Lock", "", "");
//		enhanceContractWithPredicateDetails("unLock",f, evalPath, "Lock", "", "");
//		enhanceContractWithPredicateDetails("isLocked",f, evalPath, "Lock", "", "");
		//enhanceContractWithPredicateDetails("nextDay",f, evalPath, "BankAccount", "", "");
//		
////		changeMetaproductContract("update",f, evalPath, "DailyLimit", "", getOriginalMethod("update", "DailyLimit", f));
////		changeMetaproductContract("Account",f, evalPath, "BankAccount", "", "");
//		changeMetaproductContract("Account",f, evalPath, "BankAccount", "", "");
////		//enhanceContractWithPredicateDetails("update_BankAccount",f, evalPath, "BankAccount", "", "");
//		changeMetaproductContract("update",f, evalPath, "BankAccount", "", "");
//		changeMetaproductContract("update",f, evalPath, "DailyLimit", "", "");
//		changeMetaproductContract("undoUpdate",f, evalPath, "BankAccount", "", "");
//		changeMetaproductContract("undoUpdate",f, evalPath, "DailyLimit", "", "");
//		changeMetaproductContract("calculateInterest",f, evalPath, "Interest", "", "");
//		changeMetaproductContract("estimatedInterest",f, evalPath, "InterestEstimation", "", "");
//		changeMetaproductContract("credit",f, evalPath, "CreditWorthiness", "", "");
//		changeMetaproductContract("lock",f, evalPath, "Lock", "", "");
//		changeMetaproductContract("unLock",f, evalPath, "Lock", "", "");
		changeMetaproductContract("lock",f, evalPath, "Transaction", "", "");
		
//		System.out.println(isPrototype("isLocked", "Account", "Transaction", evalPath));
//		System.out.println(isPrototype("transfer", "Transaction", "Transaction", evalPath));
//		System.out.println(isPrototype("update", "Account", "Transaction", evalPath));
	}
	
	public static boolean isPrototype(String methodName, String classname, String featureName, File evalPath) {
		File javafile = new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+featureName+FILE_SEPERATOR+classname+".java");
		try {
			String content = new String(Files.readAllBytes(javafile.toPath()), StandardCharsets.UTF_8);
        	Pattern pattern = Pattern.compile(".*\\s+"+methodName+"\\s*\\(.*\\)\\{\\}.*");
        	Matcher matcher = pattern.matcher(content);
        	if(matcher.find()) { 
        	    return true;
        	}
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return false;
	}

	
	/**
	 * Performs the proof transformation for all partial proofs if necessary
	 * @param projectDir Directory of the Project contains Directory "Partial Proofs for Metaproduct" with proofs of the featurestub
	 */
	public static void preparePartialProofs(File projectDir, File evalPath){
		File partialProofs = new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir);
		System.out.println("Prepare " + partialProofs + " for Partialproofs");
		File[] featurestubs = partialProofs.listFiles();
		//prepareMetaproductForNonRigid(new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir));
		
		//Pass 1: Add meta contract information
		for(File f : featurestubs){
			if(f.isDirectory()){
				File[] proofs = f.listFiles();
				for(File proofFile: proofs){
					if(proofFile.getName().endsWith(".proof")) {
						String methodname = getMethodName(proofFile);//undoUpdate
						String classname = getClassName(proofFile);
						if(methodname.equals("inv") || isPrototype(methodname, classname,f.getName(),evalPath)) {
							continue;
						}
						
						File metaproduct = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir+FILE_SEPERATOR+getClassName(proofFile)+".java");
						enhanceContractWithPredicateDetails(methodname,metaproduct,evalPath,f.getName(),proofFile.getName(), "");
						System.out.println("Methodname = " + methodname + "; Featurename = " + f.getName());
					}
				}
			}
		}
		
		//Pass 2: Change remaining stuff
		for(File f : featurestubs){
			if(f.isDirectory()){
				File[] proofs = f.listFiles();
				for(File proofFile: proofs){
					if(proofFile.getName().endsWith(".proof")) {

						String methodname = getMethodName(proofFile);//undoUpdate
						String method_to_replace = methodname + "_original_" + f.getName();

						replaceJavaSource(proofFile);
						File metaproduct = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir+FILE_SEPERATOR+getClassName(proofFile)+".java");
						if(checkForOriginal(proofFile,f.getName())){
							String replace_with = "dispatch_" + methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct);
							if(!checkForMethod(replace_with,metaproduct)) {
								replace_with = methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct);
							
							}
							changeMetaproductContract(methodname,metaproduct,evalPath,f.getName(),proofFile.getName(), replace_with);
							replaceMethodNamesInPartialProofs(method_to_replace,replace_with,f.getName(),proofFile);
							renameAbstractKeywords(proofFile, f, methodname);
							renameRemainingStuff(proofFile, f, methodname);
							renameProof(proofFile,f,methodname+"_"+f.getName());

						}else{
							String classname = getClassName(proofFile);
							if(!methodname.equals("inv") && !isPrototype(methodname, classname,f.getName(),evalPath)) {
								changeMetaproductContract(methodname,metaproduct,evalPath,f.getName(),proofFile.getName(), "");
							}
							
							String extensionForBankAccount = "";
							List<String> whitelist = new ArrayList<String>();
							whitelist.add("update");
							whitelist.add("undoUpdate");
							whitelist.add("nextDay");
							whitelist.add("nextYear");
							if(whitelist.contains(methodname) && f.getName().equals("BankAccount")) {
								extensionForBankAccount += "_BankAccount";
								renameRemainingStuff(proofFile, f, methodname);
							}
							renameAbstractKeywords(proofFile, f, methodname);
							
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
	 * finds all abstract contracts stuff and removes it
	 * @param metaProduct
	 */
	public static void prepareMetaproductForNonRigid(File metaProduct) {
		createKeyFile(Paths.get(metaProduct.getAbsolutePath()+FILE_SEPERATOR+"Meta.key"));
		
		for(File source : metaProduct.listFiles()){
			if(!source.isDirectory()){
					StringBuffer sbuffer = new StringBuffer();
					try {
						BufferedReader bReader = new BufferedReader(new FileReader(source));
			            String line = bReader.readLine();
			            while(line != null ) {
			            	 line = line.replace("/*@pure", "/*@ pure")
			             			.replace("pure@*/", "pure @*/").replaceAll("  ", " ").replace("/*@ pure @*/", "");
			        	     if(line.contains("_abs")) {
			                	String tmp = line.substring(0,line.indexOf("_abs")); 
			                	line = bReader.readLine();
			                	if(line.contains("def ")) {
				                	int index = line.indexOf(" = " );
				                	line = tmp + line.substring(index+2);                	
			                	}
			                } 
			            	sbuffer.append(line+ System.getProperty("line.separator"));
			                line = bReader.readLine();

			            }
			            BuilderUtil.rewriteFile(sbuffer,source);

			            bReader.close();
					}catch (Exception e) {
						 e.printStackTrace();
					}				
				}
			
		}

	}
	
	private static void enhanceContractWithPredicateDetails(String methodeName, File metaProduct,File evalPath, String featureName, String contractName, String projectName) {
		String realname = methodeName+"_"+featureName;
		try {
			if(!(new String(Files.readAllBytes(metaProduct.toPath()), StandardCharsets.UTF_8).contains(methodeName+"_"+featureName))) {
				realname = methodeName;
			}
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(metaProduct));
            String line = bReader.readLine();
            
            List<String> oldContract = new ArrayList<String>();

            int lineNr = 0;
            int j = 0;
            int contractLineNr = 0;
            boolean done = false;
            while(line != null ) {   
            	line = line.replace("/*@pure", "/*@ pure")
            			.replace("pure@*/", "pure @*/").replaceAll("  ", " ").replace("/*@ pure @*/", "");
            	
            	if(line.contains("/*@")){
            		lineNr = j;
            		if(!done)
            			oldContract.clear();
            	}            
            	if(line.contains("requires") && line.contains("FM.FeatureModel.") && !done) {
            		String tmp = line;
            		int k = tmp.lastIndexOf("FM.FeatureModel.");
            		
            		while(k< tmp.length() && tmp.charAt(k) != ' ' &&  tmp.charAt(k) != '&' &&  tmp.charAt(k) != ';') {
            			k++;
            		}
            		
            		String allowedCombination = tmp.substring(0, k);
            		String str = allowedCombination.replaceFirst("requires", "").replace("@", "").trim();
            		if(str.isEmpty())
            			str = "true";
            		oldContract.add("combination " + str);
            	} 

            	Pattern pattern = Pattern.compile(".*\\s+"+realname+"\\s*\\(.*\\)\\s*\\{");
            	Matcher matcher = pattern.matcher(line);
            	if(matcher.find()) { 
            	    contractLineNr = lineNr;
            	    done = true;
            	    break;
            	}
                line = bReader.readLine();
                j++;
            }           
            bReader.close();
            
            StringBuffer sbuffer = new StringBuffer();
            bReader = new BufferedReader(new FileReader(metaProduct));
            
            for(int i = 0 ; i <contractLineNr; i++) {
               	line = bReader.readLine();
            	if(line != null){
            		sbuffer.append(line+ System.getProperty("line.separator"));
            	}
            }
            
            if(oldContract.isEmpty()) {
            	oldContract.add("combination true");
            }
            
            if(!realname.equals(methodeName)) { //i.e., realname = methodname_featurename
	            //Extract contract of original method
	            String originalMethod = methodeName + "_" + getOriginalMethod(methodeName, featureName, metaProduct);
	            
	            String content = new String(Files.readAllBytes(metaProduct.toPath()), StandardCharsets.UTF_8);
	            String contractOfOriginal = "";
	            for(String sentence : content.split("\n")) {
	            	
	            	Pattern pattern = Pattern.compile(".*"+originalMethod+"\\s*\\(.*\\)\\s*\\{");
	            	Matcher matcher = pattern.matcher(sentence);
	            	if(matcher.find()) { 
	            		break;
	            	}
	            	System.out.println(".*"+originalMethod+"\\s*\\(.*\\)\\s*\\{");
	            	if(sentence.contains("/*@")) {
	            		contractOfOriginal = "/*@";
	            	} else {
	            		contractOfOriginal += sentence + "\n";
	            	}
	            }
	
	        	for(String sentence : contractOfOriginal.split("\n")) {
	        		if(sentence.contains("requires")) {
	        			oldContract.add("originalpre " + sentence.replaceAll("requires", "").replaceAll("@", "").replaceAll(";", "").trim());
	        		} else if(sentence.contains("ensures")) {
	        			oldContract.add("originalpost " + sentence.replaceAll("ensures", "").replaceAll("@", "").replaceAll(";", "").trim());
	        		}  else if(sentence.contains("assignable")) {
	        			oldContract.add("originalframe " + sentence.replaceAll("assignable", "").replaceAll("@", "").replaceAll(";", "").trim());
	        		}
	        	}
            }
            
            String oldContractStr = String.join("\n", oldContract);
            oldContractStr = "/*\n" + oldContractStr + "\n*/";
            
            oldContractStr = oldContractStr.replaceAll("@", "");
            oldContractStr = oldContractStr.replaceAll("combination", "\t _combination_" + realname +" =");
            oldContractStr = oldContractStr.replaceAll("originalpre", "\t _originalPre_" + realname +" =");
            oldContractStr = oldContractStr.replaceAll("originalpost", "\t _originalPost_" + realname +" =");
            oldContractStr = oldContractStr.replaceAll("originalframe", "\t _originalFrame_" + realname +" =");
             
            sbuffer.append(oldContractStr+"\n");
            while (line != null) {      
            	line = bReader.readLine();
            	if(line != null)
            		sbuffer.append(line+System.getProperty("line.separator"));
            }
            BuilderUtil.rewriteFile(sbuffer,metaProduct);
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        		
	}
	
	/**
	 * Gets the contract of the featurestub and passes it into the metaproduct
	 * @param methodeName
	 * @param metaProduct
	 * @param evalPath
	 * @param featureName
	 */
	private static void changeMetaproductContract(String methodeName, File metaProduct,File evalPath, String featureName, String contractName, String projectName) {
		File featureStub = new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+featureName+FILE_SEPERATOR+metaProduct.getName());
		String contractString = "";

		//search the featurestub for the correct contract and save it
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(featureStub));
            String line = bReader.readLine();
            
            boolean methodFound = false;
            while(line != null && !methodFound) {          	
            	line = line.replace("/*@pure", "/*@ pure")
            			.replace("pure@*/", "pure @*/").replaceAll("  ", " ").replace("/*@ pure @*/", "");
            	
            	if(line.contains("/*@")){
            		contractString = "";            		
            	    while(!line.contains("@*/") && !line.contains("*/")) {
            	    	contractString = contractString + line+ System.getProperty("line.separator");
            			line = bReader.readLine();
            		}
            	    contractString = contractString + line+ System.getProperty("line.separator");
            	    
            	    if(line != null)
            	    	line = bReader.readLine();
            	    
                	if(line.contains(methodeName+"(")) {
   					 	methodFound = true;
                	}
            	} 
				
				
				line = bReader.readLine();
            }
            contractString = contractString.replaceAll(methodeName+"_original_"+featureName, projectName);
          
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
		
		String realname = methodeName+"_"+featureName;
		try {
			if(!(new String(Files.readAllBytes(metaProduct.toPath()), StandardCharsets.UTF_8).contains(methodeName+"_"+featureName))) {
				realname = methodeName;
			}
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		//search in the metaproduct for the method and change the contract to the one from the featurestub
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(metaProduct));
            String line = bReader.readLine();
            
            List<String> oldContract = new ArrayList<String>();

            int lineNr = 0;
            int j = 0;
            int contractLineNr = 0;
            int methodLineNr = 0;
            while(line != null ) {
            	line = line.replace("/*@pure", "/*@ pure")
            			.replace("pure@*/", "pure @*/").replaceAll("  ", " ").replace("/*@ pure @*/", "");
            	
            	if(line.contains("/*@")){
            		lineNr = j;
            	}            
//            	if(line.contains("requires") && line.contains("FM.FeatureModel.") && !done) {
//            		String tmp = line;
//            		int k = tmp.lastIndexOf("FM.FeatureModel.");
//            		
//            		while(k< tmp.length() && tmp.charAt(k) != ' ' &&  tmp.charAt(k) != '&' &&  tmp.charAt(k) != ';') {
//            			k++;
//            		}
//            		
//            		String allowedCombination = tmp.substring(0, k);
//            		String str = allowedCombination.replaceFirst("requires", "").replace("@", "").trim();
//            		if(str.isEmpty())
//            			str = "true";
//            		oldContract.add("combination " + str);
//            	} 

            	Pattern pattern = Pattern.compile(".*\\s+"+realname+"\\s*\\(.*\\)\\s*\\{");
            	Matcher matcher = pattern.matcher(line);
            	if(matcher.find()) { 
            	    contractLineNr = lineNr;
            	    methodLineNr = j;
            	    //done = true;
            	    //break;
            	}
//            	if(line.matches(".*"+realname+"\\s*\\(.*\\)\\s*\\{.*")) { 
//            	    contractLineNr = lineNr;
//            	    methodLineNr = j;
//            	    done = true;
//            	}
                line = bReader.readLine();
                j++;
            }           
            bReader.close();
            
            StringBuffer sbuffer = new StringBuffer();
            bReader = new BufferedReader(new FileReader(metaProduct));
            for(int i = 0 ; i <= methodLineNr; i++) {
            	if(i > contractLineNr) {
            		line = "";
            	}else if(line != null){
            	sbuffer.append(line+ System.getProperty("line.separator"));
            	}
            	line = bReader.readLine();
            }
            
//            if(oldContract.isEmpty()) {
//            	oldContract.add("combination true");
//            }
            
//            if(!realname.equals(methodeName)) { //i.e., realname = methodname_featurename
//	            //Extract contract of original method
//	            String originalMethod = methodeName + "_" + getOriginalMethod(methodeName, featureName, metaProduct);
//	            
//	            String content = new String(Files.readAllBytes(metaProduct.toPath()), StandardCharsets.UTF_8);
//	            String contractOfOriginal = "";
//	            for(String sentence : content.split("\n")) {
//	            	
//	            	Pattern pattern = Pattern.compile(".*"+originalMethod+"\\s*\\(.*\\)\\s*\\{");
//	            	Matcher matcher = pattern.matcher(sentence);
//	            	if(matcher.find()) { 
//	            		break;
//	            	}
//	            	System.out.println(".*"+originalMethod+"\\s*\\(.*\\)\\s*\\{");
//	            	if(sentence.contains("/*@")) {
//	            		contractOfOriginal = "/*@";
//	            	} else {
//	            		contractOfOriginal += sentence + "\n";
//	            	}
//	            }
	
//	        	for(String sentence : contractOfOriginal.split("\n")) {
//	        		if(sentence.contains("requires")) {
//	        			oldContract.add("originalpre " + sentence.replaceAll("requires", "").replaceAll("@", "").replaceAll(";", "").trim());
//	        		} else if(sentence.contains("ensures")) {
//	        			oldContract.add("originalpost " + sentence.replaceAll("ensures", "").replaceAll("@", "").replaceAll(";", "").trim());
//	        		}  else if(sentence.contains("assignable")) {
//	        			oldContract.add("originalframe " + sentence.replaceAll("assignable", "").replaceAll("@", "").replaceAll(";", "").trim());
//	        		}
//	        	}
//            }
            
//            String oldContractStr = String.join("\n", oldContract);
//            oldContractStr = "/*\n" + oldContractStr + "\n*/";
//            
//            oldContractStr = oldContractStr.replaceAll("@", "");
//            oldContractStr = oldContractStr.replaceAll("combination", "\t _combination_" + realname +" =");
//            oldContractStr = oldContractStr.replaceAll("originalpre", "\t _originalPre_" + realname +" =");
//            oldContractStr = oldContractStr.replaceAll("originalpost", "\t _originalPost_" + realname +" =");
//            oldContractStr = oldContractStr.replaceAll("originalframe", "\t _originalFrame_" + realname +" =");
             
            sbuffer.append(contractString);
            while (line != null) {          	
            	sbuffer.append(line+ System.getProperty("line.separator"));
				line = bReader.readLine();
            }
            BuilderUtil.rewriteFile(sbuffer,metaProduct);
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
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
            		line = "\\javaSource \"../../../../../../"+folderString+"/src\";" +

            		//line = "\\javaSource \".."+FILE_SEPERATOR+".."+FILE_SEPERATOR+"src\";"+
            		//line = line + 
            				"\n\n"+ "\\functions {\n" + 
            				"  LocSet OriginalFrame;\n" + 
            				"}\n" + 
            				"\n" + 
            				"\\predicates {\n" + 
            				"  \\nonRigid OriginalPre;\n" + 
            				"  \\nonRigid OriginalPost;\n" + 
            				"  \\nonRigid AllowedFeatureCombination;\n" + 
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
	/**
	 * 
	 * @param file
	 */
	private static void createKeyFile(Path file) {
		String text = "\\javaSource \".\";\n" + 
				"\n" + 
				"\\functions {\n" + 
				"  LocSet OriginalFrame;\n" + 
				"}\n" + 
				"\n" + 
				"\\predicates {\n" + 
				"  \\nonRigid OriginalPre;\n" + 
				"  \\nonRigid OriginalPost;\n" + 
				"  \\nonRigid AllowedFeatureCombination;\n" + 
				"}\n" + 
				"\n" + 
				"\\chooseContract";
		try {
			Files.deleteIfExists(file);			
			Files.write(file, text.getBytes("UTF-8"));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
}

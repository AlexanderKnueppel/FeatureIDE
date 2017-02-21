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
import java.io.FileReader;
import java.io.IOException;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;

/**
 * 
 * Contains the methods which works on the metaproduct to adapte the code for key
 * 
 * @author Stefanie
 */
public class MetaProductBuilder {
	
	public static String FILE_SEPERATOR = System.getProperty("file.separator");
	
	/**
	 * Prepares the metaproduct for verification
	 * @param metaproductLocation src folder which contains the metaproduct
	 */
	public static void prepareMetaProduct(File metaproductLocation){
		File account = new File(metaproductLocation.getAbsolutePath()+FILE_SEPERATOR+"Account.java");
		BuilderUtil.removeBracketsOfVar(account, "lock");
		BuilderUtil.removeBracketsOfVar(account, "result");
	}
	
	/**
	 * Performs the proof transformation for all partial proofs if necessary
	 * @param projectDir Directory of the Project contains Directory "Partial Proofs for Metaproduct" with proofs of the featurestub
	 */
	public static void preparePartialProofs(File projectDir, File evalPath){
		File partialProofs = new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir);
		File[] featurestubs = partialProofs.listFiles();
		for(File f : featurestubs){
			if(f.isDirectory()){
				File[] proofs = f.listFiles();
				for(File proof: proofs){
					String methodname = getMethodName(proof);
					File metaproduct = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir+FILE_SEPERATOR+getClassName(proof)+".java");
					if(checkForOriginal(proof,f.getName())||checkForMethod(methodname+"_"+f.getName(),metaproduct)){
						replaceMethodNamesInPartialProofs(methodname,methodname+"_"+getOriginalMethod(methodname,f.getName(),metaproduct),f.getName(),proof);
						renameProof(proof,f,methodname+"_"+f.getName());
					}
					else{
						renameProof(proof,f,methodname);
					}
				}
			}
		}
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
	 * Returns true if the given file contains an orginial call with methodname_original_featurestub
	 * @param f
	 * @param featurestub
	 * @return
	 */
	private static boolean checkForOriginal(File f, String featurestub){
		if(f.getAbsolutePath().endsWith(".proof")&!f.getAbsolutePath().contains("inv")){
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
	private static boolean checkForMethod(String method, File metaproductClass){
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
	 * @param currentMethodName methodname in the featurestub
	 * @param originalMethod methodname_originalMethod methodname of the originalcall in the metaproduct
	 * @param featurestub 
	 * @param proof
	 */
	private static void replaceMethodNamesInPartialProofs(String currentMethodName,String originalMethod
			,String featurestub, File proof){
		StringBuffer sbuffer = new StringBuffer();
		String originalCall = currentMethodName+"_original_"+featurestub;
		String newMethodName = currentMethodName+"_"+featurestub;
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(proof));
            String line = bReader.readLine();
            while(line != null) {
            	if(line.contains(originalCall)){
            		line = line.replaceAll(originalCall, originalMethod);
            		String[] seperatedLine = line.split(currentMethodName);
            		line = "";
            		boolean firstElement = true;
            		for(String s: seperatedLine){
            			if(firstElement){
            				firstElement = false;
            			}
            			else{
            				s = currentMethodName + s;
            			}
            			if(!s.contains(originalMethod)){
            				s = s.replace(currentMethodName, newMethodName );
            			}
            			line += s;
            		}
                }
            	else if(line.contains(currentMethodName)){
            		line = line.replaceAll(currentMethodName, newMethodName);
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
}

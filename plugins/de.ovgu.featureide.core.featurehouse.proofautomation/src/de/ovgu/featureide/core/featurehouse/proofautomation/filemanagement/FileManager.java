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
package de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.parser.KeYLexerTokensUpdaterParser.finallyClause_return;

/**
 * 
 * Contains methods for file organisation
 * 
 * @author Stefanie
 */
public class FileManager {
	//Needed directories for verification
	public final static String evaluationDir = "Evaluation"; //directory that contains all generated files for evaluation
	public final static String featuresDir = "features"; //directory of features
	public final static String metaproductDir = "src"; //directory that contains the metaproduct
	public final static String featureStubDir = "featurestub"; //directory that contains the Featurestubs
	public final static String partialProofsDir = "Partial Proofs for Metaproduct";// directory that contains the modified abstract proof part
	public final static String finishedProofsDir = "Finished Proofs"; //directory that contains the finished proof
	public final static String savedProofsDir = "Saved Proofs";  // directory that contains the finished abstract proof part
	public final static String projectName = "BankAccount"; //Name of the projects, to check whether a directory is a project for evaluation
	public static String FILE_SEPERATOR = System.getProperty("file.separator");
	public static DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd HH-mm-ss");
	
	/**
	 * Creates a time stamp directory
	 * @param d
	 * @param location
	 * @return
	 */
	public static File createDateDir(Date d, File location){
		String dirName = dateFormat.format(d);
		File newDir = new File(location.getAbsolutePath()+FILE_SEPERATOR+dirName);
		createDir(newDir);
		return newDir;
	}

	/**
	 * Returns the first java file of the metaproduct
	 * needed as parameter for key
	 * 
	 * @param projectDir
	 * @return
	 */
	public static File getFirstMetaproductElement(File projectDir){
		File metaproductPath = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+metaproductDir);
		return getFirstJavaFile(metaproductPath,metaproductPath.list());
	}
	
	/**
	 * Returns a list with one java file for each featurestub
	 * @param projectDir directory of the project
	 * @return
	 */
	public static List<File> getAllFeatureStubFilesOfAProject(File projectDir){
		File featurestubPath = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+featureStubDir);
		String[] featurestubDir = featurestubPath.list();
		List<File> featureStubFirstFile = new ArrayList<File>();
		for(String featurestub: featurestubDir){
			File featurestubpath = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+featureStubDir+FILE_SEPERATOR+featurestub);
			String[] featurestubContent = featurestubpath.list();
			if(featurestubContent!= null){
				File firstJava = getFirstJavaFile(featurestubpath,featurestubContent);
				if(firstJava != null){
					featureStubFirstFile.add(firstJava);
				}
			}
		}
		return featureStubFirstFile;
	}
	
	/**
	 * Returns the first java file of the directory
	 * needed as parameter for key
	 * @param path
	 * @param srcDir
	 * @return
	 */
	private static File getFirstJavaFile(File path,String[] srcDir){
		for(String file : srcDir){
			if(file.matches(".*\\.key")) {
				return new File (path.getAbsolutePath()+FILE_SEPERATOR+file);
			}
		}
		for(String file : srcDir){
			if(file.matches(".*\\.java")){
				return new File (path.getAbsolutePath()+FILE_SEPERATOR+file);
			}
		}
		return null;
	}
	
	/**
	 * Initializes the necessary folders for the verification
	 * @param evaluateDir
	 * @param version
	 */
	public static void initFolders(File evaluateDir, int version){
		if(version ==1 || version == 2 || version == 7 || version  == 8){
			createDir(new File(evaluateDir+FILE_SEPERATOR+savedProofsDir));
			createDir(new File(evaluateDir+FILE_SEPERATOR+partialProofsDir));
			if(version==1){
				createDir(new File(evaluateDir+FILE_SEPERATOR+featureStubDir));
			}
		}
		createDir(new File(evaluateDir+FILE_SEPERATOR+finishedProofsDir));
		createDir(new File(evaluateDir+FILE_SEPERATOR+metaproductDir));
	}
	
	/**
	 * Creates the directory if it doesn't exist
	 * @param dir
	 * @return
	 */
	public static File createDir(File dir){
		if(!dir.exists()){
			dir.mkdir();
		}
		return dir;
	}
	
	/**
	 * Copys the directory with saved proofs from the first phase to the partial proofs for metaproduct directory
	 * @param evalDir
	 */
	public static void copySavedProofsToPartialProofs(File evalDir){
		File savedProofs = new File(evalDir.getAbsolutePath()+FILE_SEPERATOR+savedProofsDir);
		File[] saved = savedProofs.listFiles();
		for(File f: saved){
			if(f.isDirectory()){
				File newDir = new File(evalDir.getAbsolutePath()+FILE_SEPERATOR+partialProofsDir+FILE_SEPERATOR+f.getName());
				createDir(newDir);
				File[] inDir = f.listFiles();
				for(File i : inDir){
					copyFile(i.getAbsolutePath(),newDir.getAbsolutePath()+FILE_SEPERATOR+i.getName());
				}
			}
		}
	}
	
	/**
	 * Copys a single file from src to target
	 * @param src
	 * @param target
	 */
	private static void copyFile(String src, String target){
		Path source = Paths.get(src);
	    Path destination = Paths.get(target);
	    try {
	    	if(!destination.toFile().exists()){
	    		Files.copy(source, destination);
	    	}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	/**
	 * Copies files from folder version1 to versionX
	 * @param version1
	 * @param versionX
	 */
	public static void copyFolderContent(File version1, File versionX){
		if(version1.isDirectory()&&versionX.isDirectory()){
			File[] allPartialProofs = version1.listFiles();
			for(File f: allPartialProofs){
				copyFile(f.getAbsolutePath(),versionX.getAbsolutePath()+FILE_SEPERATOR+f.getName());
			}
		}
	}
	
	/**
	 * Copies files from folder version1 to versionX
	 * @param version1
	 * @param versionX
	 */
	public static void copyCompleteFolderContent(File folderSrc, File folderTarget){
		if(folderSrc.isDirectory()&&folderTarget.isDirectory()){
			File[] allPartialProofs = folderSrc.listFiles();
			for(File f: allPartialProofs){
				copyFile(f.getAbsolutePath(),folderTarget.getAbsolutePath()+FILE_SEPERATOR+f.getName());
				if(f.isDirectory()){
					copyCompleteFolderContent(f,new File(folderTarget.getAbsolutePath()+FILE_SEPERATOR+f.getName()));
				}
			}
		}
	}
	
	/**
	 * Copies the reusable proofs for featurestubs of previous versions
	 * @param evalPath
	 * @param project
	 */
	public static void reuseFeaturestub(File evalPath, File project){
		try{
			//TODO quicky fixi... don't know about that => change project to evalPath????
			File firstProjectFeaturestub = new File(getProjectv1Path(project).getAbsolutePath()+FILE_SEPERATOR+featureStubDir);
			File firstProjectSavedProofs = new File(getProjectv1Path(evalPath).getAbsolutePath()+FILE_SEPERATOR+savedProofsDir);
			File currentProjectFeaturestub =new File(project.getAbsolutePath()+FILE_SEPERATOR+featureStubDir);
			List<File> equalFeaturestubs = compareFeatureStubs(currentProjectFeaturestub,firstProjectFeaturestub);
			System.out.println("Reusing the following feature stubs for " + project.getName());
			for(File e: equalFeaturestubs){
				System.out.println(e.getName());
				File savedProofFeaturestub = new File(firstProjectSavedProofs+FILE_SEPERATOR+e.getName());
				File[] reusableProofs= savedProofFeaturestub.listFiles();
				for(File r: reusableProofs){
					File savedProofFeaturestubCur =new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+savedProofsDir+FILE_SEPERATOR+e.getName());
					System.out.println("Reuse: " + r.getName());
					createDir(savedProofFeaturestubCur);
					copyFile(r.getAbsolutePath(),savedProofFeaturestubCur+FILE_SEPERATOR+r.getName());
				}
			}
		} catch(Exception e){
			System.out.println(e.getMessage() + "\n" + "Single Project Excecution finds no reuse");
		}
	}
	
//	public static void main(String[] args) {
//		File ba1stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\reverifyEqual\\BankAccountv1"+FILE_SEPERATOR+featureStubDir);
//		File ba2stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\reverifyEqual\\Evaluation\\2019-11-27 07-57-21\\1\\BankAccountv7"+FILE_SEPERATOR+featureStubDir);
//		for(File f : compareFeatureStubs(ba1stubs, ba2stubs)) {
//			System.out.println(f.getName() + " is the same!");
//		}
//		
//		File project = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\reverifyEqual\\BankAccountv7");
//		File evalPath = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\reverifyEqual\\Evaluation\\2019-11-27 07-57-21\\1\\BankAccountv7");
//		reuseFeaturestub(evalPath, project);
//	}
	
	public static void main(String[] args) {
		File ba1stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv1"+FILE_SEPERATOR+featureStubDir);
		File ba2stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv2"+FILE_SEPERATOR+featureStubDir);
		for(File f : compareFeatureStubs(ba1stubs, ba2stubs)) {
			System.out.println(f.getName() + " is the same!");
		}
//		
		File first = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv2");
		File second = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv2");
		reuseFeaturestub(first, second);
	}
	
	/**
	 * Returns all featurestub files which are equal 
	 * @param fstubA
	 * @param fstubB
	 * @return
	 */
	private static LinkedList<File> compareFeatureStubs(File fstubA, File fstubB){
		if(!fstubA.isDirectory()||!fstubB.isDirectory()){
			return null;
		}
		File[] dirAFiles = fstubA.listFiles();
		File[] dirBFiles = fstubB.listFiles();
		LinkedList<File> equalFeatureStubs = new LinkedList<File>();
		for(File a : dirAFiles){
			for(File b : dirBFiles){
				if(a.getName().equals(b.getName())){
					if(compareDirectory(a,b)){
						equalFeatureStubs.add(b);
					}
				}
			}
		}
		return equalFeatureStubs;
	}
	
	/**
	 * Returns the equal files of both directories
	 * @param dirA
	 * @param dirB
	 * @return
	 */
	private static boolean compareDirectory(File dirA, File dirB){
		if(!dirA.isDirectory()||!dirB.isDirectory()){
			return false;
		}
		File[] dirAFiles = dirA.listFiles();
		File[] dirBFiles = dirB.listFiles();
		for(File a : dirAFiles){
			for(File b : dirBFiles){
				if(a.getName().equals(b.getName())){
					if(!filesAreEqual(a,b)){
						return false;
					}
				}
			}
		}
		return true;
	}
	
	/**
	 * Compares two files 
	 * @param a
	 * @param b
	 * @return true if the files are equal
	 */
	private static boolean filesAreEqual(File a, File b){
		try {
			byte[] aBytes = Files.readAllBytes(a.toPath());
			byte[] bBytes = Files.readAllBytes(b.toPath());
			if(aBytes.length!=bBytes.length){
//				System.out.println(a.getAbsolutePath() + ": " + aBytes.length + " bytes");
//				System.out.println(b.getAbsolutePath() + ": " + bBytes.length + " bytes");
				return false;
			}
			for(int i = 0; i< aBytes.length;i++){
				if(aBytes[i]!=bBytes[i]){
					return false;
				}
			}
			return true;
		} catch (IOException e) {
			e.printStackTrace();
		}
		return false;
	}
	
	
	/**
	 * Returns the Path of BankAccountv1 of the current approach
	 * @param location
	 * @return
	 */
	public static File getProjectv1Path(File location){
		File parentPath = location.getParentFile();
		File[] allProjects = parentPath.listFiles();
		File firstProject = null;
		for(File project : allProjects){
			if(project.getName().contains("1")&&project.isDirectory()){
				firstProject = project;
			}
		}
		return firstProject;
	}
}

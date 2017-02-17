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

/**
 * 
 * Contains methods for file organisation
 * 
 * @author Stefanie
 */
public class FileManager {
	//Needed directories for verification
	public final static String evaluationDir = "Evaluation"; //directory that contains all generated files for evaluation
	public final static String metaproductDir = "src"; //directory that contains the metaproduct
	public final static String featureStubDir = "featurestub"; //directory that contains the Featurestubs
	public final static String partialProofsDir = "Partial Proofs for Metaproduct";// directory that contains the modified abstract proof part
	public final static String finishedProofsDir = "Finished Proofs"; //directory that contains the finished proof
	public final static String savedProofsDir = "Saved Proofs";  // directory that contains the finished abstract proof part
	public final static String projectName = "BankAccount"; //Name of the projects, to check wether a directory is a project for evaluation
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
	 * Returns the directory which was created last
	 * @param project
	 * @return
	 */
	public static File getCurrentEvaluationPath(File project){
		File evalPath = new File(project.getAbsolutePath()+FILE_SEPERATOR+evaluationDir);
		File[] subDirs = evalPath.listFiles();
		File currentEvalPath = null;
		for(File s: subDirs){
			if(currentEvalPath == null){
				currentEvalPath = s;
			}
			if(s.getName().compareTo(currentEvalPath.getName()) > 0){
				currentEvalPath = s;
			}
		}
		return currentEvalPath;
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
		if(version ==1 || version == 2){
			createDir(new File(evaluateDir+FILE_SEPERATOR+savedProofsDir));
			createDir(new File(evaluateDir+FILE_SEPERATOR+partialProofsDir));
		}
		createDir(new File(evaluateDir+FILE_SEPERATOR+finishedProofsDir));
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
	public static void copyFile(String src, String target){
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
	 * Copies the partial proofs from a previous version, which can be reused by the current version
	 * @param versionA
	 * @param versionB
	 */
	public static void copyReusablePartialProofs (File versionA, File versionB){
		if(versionA.isDirectory()&&versionB.isDirectory()){
			File featureStubA = new File(versionA.getAbsolutePath()+FILE_SEPERATOR+featureStubDir);
			File featureStubB = new File(versionB.getAbsolutePath()+FILE_SEPERATOR+featureStubDir);
			List<File> equalFeaturestubfiles = compareFeatureStubs(featureStubA,featureStubB);
			createDir(new File(versionB.getAbsolutePath()+FILE_SEPERATOR+savedProofsDir));
			File[] featurestubs = featureStubB.listFiles();
			for(File f : featurestubs){
				if(f.isDirectory()){
					createDir(new File(versionB.getAbsolutePath()+FILE_SEPERATOR+savedProofsDir+FILE_SEPERATOR+f.getName()));
				}
			}
			for(File e: equalFeaturestubfiles){
				List<File> relatedProofs = getProofsForFeatureStubClass(e,versionA);
				for(File rp: relatedProofs){
					copyFile(rp.getAbsolutePath(),versionB.getAbsolutePath()+FILE_SEPERATOR+savedProofsDir+FILE_SEPERATOR+e.getParentFile().getName());
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
		File firstProject = getProjectv1Path(project);
		File firstProjectEvalPath = new File(firstProject.getAbsolutePath()+FILE_SEPERATOR+evaluationDir);
		List<File> equalFiles = compareFeatureStubs(new File(project.getAbsolutePath()+FILE_SEPERATOR+featureStubDir),new File(firstProject.getAbsolutePath()+FILE_SEPERATOR+featureStubDir));
		for(File f: equalFiles){
			List<File> reusableProofs= getProofsForFeatureStubClass(f,firstProjectEvalPath);
			for(File r: reusableProofs){
				createDir(new File(getCurrentEvaluationPath(project)+FILE_SEPERATOR+savedProofsDir+FILE_SEPERATOR+f.getParentFile().getName()));
				copyFile(r.getAbsolutePath(),getCurrentEvaluationPath(project)+FILE_SEPERATOR+savedProofsDir+FILE_SEPERATOR+f.getParentFile().getName()+FILE_SEPERATOR+r.getName());
			}
		}
	}
	
	/**
	 * Returns a filelist which contains all proofs which belongs to the given featurestub class
	 * @param featureStubClass
	 * @param versionA
	 * @return
	 */
	public static List<File> getProofsForFeatureStubClass(File featureStubClass, File versionA){
		File featurestub = featureStubClass.getParentFile();
		String featureStubClassName = featureStubClass.getName().replace(".java", "");
		File previousFS = new File(getCurrentEvaluationPath(versionA.getParentFile())+FILE_SEPERATOR+savedProofsDir+FILE_SEPERATOR+featurestub.getName());
		File[] savedProofsOfFeatureStub = previousFS.listFiles();
		List<File> relatedProofs = new LinkedList<File>();
		for(File f : savedProofsOfFeatureStub){
			if(f.getName().contains(featureStubClassName)){
				relatedProofs.add(f);
			}
		}
		return relatedProofs;
	}
	
	/**
	 * Returns all featurestub files which are equal 
	 * @param fstubA
	 * @param fstubB
	 * @return
	 */
	public static List<File> compareFeatureStubs(File fstubA, File fstubB){
		if(!fstubA.isDirectory()||!fstubB.isDirectory()){
			return null;
		}
		File[] dirAFiles = fstubA.listFiles();
		File[] dirBFiles = fstubB.listFiles();
		LinkedList<File> equalFiles = new LinkedList<File>();
		for(File a : dirAFiles){
			for(File b : dirBFiles){
				if(a.getName().equals(b.getName())){
					equalFiles.addAll(compareDirectory(a,b));
				}
			}
		}
		return equalFiles;
	}
	
	/**
	 * Returns the equal files of both directories
	 * @param dirA
	 * @param dirB
	 * @return
	 */
	public static List<File> compareDirectory(File dirA, File dirB){
		if(!dirA.isDirectory()||!dirB.isDirectory()){
			return null;
		}
		File[] dirAFiles = dirA.listFiles();
		File[] dirBFiles = dirB.listFiles();
		LinkedList<File> equalFiles = new LinkedList<File>();
		for(File a : dirAFiles){
			for(File b : dirBFiles){
				if(a.getName().equals(b.getName())){
					if(filesAreEqual(a,b)){
						equalFiles.add(a);
					}
				}
			}
		}
		return equalFiles;
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

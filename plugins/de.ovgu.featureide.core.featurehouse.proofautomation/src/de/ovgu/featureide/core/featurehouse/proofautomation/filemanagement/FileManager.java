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
	public static DateFormat dateFormat = new SimpleDateFormat("dd-MM-yyyy HH-mm-ss");
	
	public static File createDateDir(Date d, File location){
		String dirName = dateFormat.format(d);
		File newDir = new File(location.getAbsolutePath()+FILE_SEPERATOR+dirName);
		createDir(newDir);
		return newDir;
	}
	
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
	
	public static File getFirstMetaproductElement(File projectDir){
		File metaproductPath = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+metaproductDir);
		return getFirstJavaFile(metaproductPath,metaproductPath.list());
	}
	
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
	
	private static File getFirstJavaFile(File path,String[] srcDir){
		for(String file : srcDir){
			if(file.matches(".*\\.java")){
				return new File (path.getAbsolutePath()+FILE_SEPERATOR+file);
			}
		}
		return null;
	}
	
	public static void initFolders(File evaluateDir, int version){
		if(version ==1 || version == 2){
			createDir(new File(evaluateDir+FILE_SEPERATOR+savedProofsDir));
			createDir(new File(evaluateDir+FILE_SEPERATOR+partialProofsDir));
		}
		createDir(new File(evaluateDir+FILE_SEPERATOR+finishedProofsDir));
	}
	
	public static File createDir(File dir){
		if(!dir.exists()){
			dir.mkdir();
		}
		return dir;
	}
	
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
	public static void copyFile(String src, String target){
		Path source = Paths.get(src);
	    Path destination = Paths.get(target);
	    try {
			Files.copy(source, destination);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
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
	
	public static List<File> getProofsForFeatureStubClass(File featureStubClass, File versionA){
		File featurestub = featureStubClass.getParentFile();
		String featureStubClassName = featureStubClass.getName().replace(".java", "");
		File[] savedProofsOfFeatureStub = (new File(versionA.getAbsolutePath()+FILE_SEPERATOR+savedProofsDir+FILE_SEPERATOR+featurestub.getName())).listFiles();
		List<File> relatedProofs = new LinkedList<File>();
		for(File f : savedProofsOfFeatureStub){
			if(f.getName().contains(featureStubClassName)){
				relatedProofs.add(f);
			}
		}
		return relatedProofs;
	}
	
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
					if(a.compareTo(b)==0){
						equalFiles.add(a);
					}
				}
			}
		}
		return equalFiles;
	}
	
}

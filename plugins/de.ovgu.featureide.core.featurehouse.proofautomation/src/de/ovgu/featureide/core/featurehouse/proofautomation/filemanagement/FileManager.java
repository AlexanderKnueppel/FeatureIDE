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
import java.util.ArrayList;
import java.util.List;

public class FileManager {
	public static String FILE_SEPERATOR = System.getProperty("file.separator");
	
	public static File getFirstMetaproductElement(File projectDir){
		File metaproductPath = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"src");
		return getFirstJavaFile(metaproductPath,metaproductPath.list());
	}
	
	public static List<File> getAllFeatureStubFilesOfAProject(File projectDir){
		File featurestubPath = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"featurestub");
		String[] featurestubDir = featurestubPath.list();
		List<File> featureStubFirstFile = new ArrayList<File>();
		for(String featurestub: featurestubDir){
			File featurestubpath = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+featurestub);
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
	
	public static void initFolders(File projectDir){
		createDir(new File(projectDir+FILE_SEPERATOR+"Saved Proofs"));
		createDir(new File(projectDir+FILE_SEPERATOR+"Partial Proofs for Metaproduct"));
		createDir(new File(projectDir+FILE_SEPERATOR+"Finished Proofs"));
	}
	
	public static void createDir(File dir){
		if(!dir.exists()){
			dir.mkdir();
		}
	}
	
	public static void copySavedProofsToPartialProofs(File projectDir){
		File savedProofs = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"Saved Proofs");
		File[] saved = savedProofs.listFiles();
		for(File f: saved){
			if(f.isDirectory()){
				File newDir = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"Partial Proofs for Metaproduct"+FILE_SEPERATOR+f.getName());
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
}

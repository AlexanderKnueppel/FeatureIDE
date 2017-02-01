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

import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_STUBS_GENERATION_STARTED_;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.LinkedList;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.featurehouse.contracts.ContractProcessor;
import de.ovgu.featureide.featurehouse.meta.FeatureStubsGenerator;

public class BuilderUtil {
	
	public static LinkedList<IProject> getProjectsByApproach(String approachName){
		IWorkspaceRoot myWorkspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		IProject[] allProjects = myWorkspaceRoot.getProjects();
		LinkedList<IProject> allProjectsForApproach = new LinkedList<IProject>();
		for(IProject p: allProjects){
			File f = p.getLocation().toFile();
			if(f.getParentFile().getName().equals(approachName)){
				allProjectsForApproach.add(p);
			}
		}
		return allProjectsForApproach;
	}
	
	/**
	 * Writes a StringBuffer into File f
	 * @param sbuffer
	 * @param f
	 */
	public static void rewriteFile(StringBuffer sbuffer,File f){
		try {
			FileWriter fw = new FileWriter(f);
        	BufferedWriter bWriter = new BufferedWriter(fw);
            bWriter.write(sbuffer.toString());
            bWriter.flush();
            bWriter.close();
            fw.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
	}
	
	public static void removeBracketsOfVar(File f,String var){
		StringBuffer sbuffer = new StringBuffer();
		String varPattern = ".*\\(\\s*"+var+"\\s*\\).*";
		String varBracket = "\\(\\s*"+var+"\\s*\\)";
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(f));
            String line = bReader.readLine();
            while(line != null) {
            	if(Pattern.matches(varPattern, line)){
            		line = line.replaceAll(varBracket, var);
                }
            	sbuffer.append(line + System.getProperty("line.separator"));
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,f);
	}
}

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

import java.io.File;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.meta.FeatureStubsGenerator;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

/**
 * TODO description
 * 
 * @author Stefanie
 */
public class projectWorker {
	
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
	
	public static void generateAllFeatureStubsForApproach(LinkedList<IProject> projects){
		for(IProject p: projects){
			try{
				final IResource res = (IResource) SelectionWrapper.checkClass(p, IResource.class);
				final IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
				if (featureProject != null) {
					FeatureStubsGenerator fsg = new FeatureStubsGenerator(featureProject);
					Job[] previousJobs =Job.getJobManager().find(null);
					fsg.generate();
					Thread.sleep(300);
//					waitForJobs(previousJobs);
				}
			} catch(Exception e){
				System.out.println("Error building featurestub:");
				//e.printStackTrace();
			}
		}
	}
	
	private static void waitForJobs(Job[] previousJobs){
		Job[] currentJobs =Job.getJobManager().find(null);
		for(Job j1: currentJobs){
			if(isNewJob(j1,previousJobs)){
				while((j1.getState()==Job.RUNNING || j1.getState()==Job.WAITING) && j1.getName().equals("Update Progress"));
			}
		}
	}
	
	private static boolean isNewJob(Job j, Job[] previousJobs){
		for(Job previousJob: previousJobs){
			if(j.equals(previousJob)){
				return false;
			}
		}
		return true;
	}
	
	public static void generateAllMetaproductsForApproach(LinkedList<IProject> projects, boolean newMetaproduct){
		for(IProject p: projects){
			try{
				IFeatureProject f = CorePlugin.getFeatureProject(p);
				FeatureHouseComposer featureHouseComposer = (FeatureHouseComposer) f.getComposer();
				featureHouseComposer.setBuildMetaProduct(true);
				IFile config = f.getCurrentConfiguration();
				if(newMetaproduct){
					f.setMetaProductGeneration(IFeatureProject.META_THEOREM_PROVING_DISP);
				}
				else{
					f.setMetaProductGeneration(IFeatureProject.META_THEOREM_PROVING);
				}
				featureHouseComposer.performFullBuild(config);
			} catch(Exception e){
				System.out.println("Error building Metaproduct "+p.getName());
				e.printStackTrace();
			}
		}
	}
}

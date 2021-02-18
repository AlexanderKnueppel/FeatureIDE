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
package de.ovgu.featureide.core.featurehouse.proofautomation.key;

/**
 * TODO description
 * 
 * @author marlen
 */
public class Record {
	
	/**
	 * @param combination
	 * @param originalPre
	 * @param originalPost
	 * @param originalFrame
	 * @param originalMethod
	 */
	public Record(String combination, String originalPre, String originalPost, String originalFrame,
			String originalMethod) {
		super();
		this.combination = combination;
		this.originalPre = originalPre;
		this.originalPost = originalPost;
		this.originalFrame = originalFrame;
		this.originalMethod = originalMethod;
	}
	
	public Record() {};
	private String combination= "";
	private String originalPre = "";
	private String originalPost = "";
	private String originalFrame = "";
	private String originalMethod = "";
	private boolean isPrepared = false;
	/**
	 * @return the isPrepared
	 */
	public boolean isPrepared() {
		return isPrepared;
	}

	/**
	 * @param isPrepared the isPrepared to set
	 */
	public void setPrepared(boolean isPrepared) {
		this.isPrepared = isPrepared;
	}

	/**
	 * @return the combination
	 */
	public String getCombination() {
		return combination;
	}
	/**
	 * @param combination the combination to set
	 */
	public void setCombination(String combination) {
		this.combination = combination;
	}
	/**
	 * @return the originalPre
	 */
	public String getOriginalPre() {
		return originalPre;
	}
	/**
	 * @param originalPre the originalPre to set
	 */
	public void setOriginalPre(String originalPre) {
		this.originalPre = originalPre;
	}
	/**
	 * @return the originalPost
	 */
	public String getOriginalPost() {
		return originalPost;
	}
	/**
	 * @param originalPost the originalPost to set
	 */
	public void setOriginalPost(String originalPost) {
		this.originalPost = originalPost;
	}
	/**
	 * @return the originalFrame
	 */
	public String getOriginalFrame() {
		return originalFrame;
	}
	/**
	 * @param originalFrame the originalFrame to set
	 */
	public void setOriginalFrame(String originalFrame) {
		this.originalFrame = originalFrame;
	}
	/**
	 * @return the originalMethod
	 */
	public String getOriginalMethod() {
		return originalMethod;
	}
	/**
	 * @param originalMethod the originalMethod to set
	 */
	public void setOriginalMethod(String originalMethod) {
		this.originalMethod = originalMethod;
	}

		
	
}

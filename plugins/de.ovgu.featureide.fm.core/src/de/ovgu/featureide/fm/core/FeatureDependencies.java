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
package de.ovgu.featureide.fm.core;

import java.util.Set;

import de.ovgu.featureide.fm.core.base.FeatureUtilsLegacy;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * This class is a legacy class for Fuji to keep working.
 * 
 * @deprecated Use {@link FeatureDependencies2} instead.
 * @author Sebastian Krieter
 * @author Stefan Krueger
 */
@Deprecated
public class FeatureDependencies extends FeatureDependencies2 {

	public FeatureDependencies(IFeatureModel fm, boolean calculateDependencies) {
		super(fm, calculateDependencies);
	}

	public FeatureDependencies(IFeatureModel fm) {
		super(fm);
	}

	public Set<IFeature> always(Feature feature) {
		return always.get(FeatureUtilsLegacy.convert(feature));
	}

	public Set<IFeature> never(Feature feature) {
		return never.get(FeatureUtilsLegacy.convert(feature));
	}

	public Set<IFeature> maybe(Feature feature) {
		return maybe.get(FeatureUtilsLegacy.convert(feature));
	}
}

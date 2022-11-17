//
// Copyright (c) 2009-2010 Mikko Mononen memon@inside.org
//
// This software is provided 'as-is', without any express or implied
// warranty.  In no event will the authors be held liable for any damages
// arising from the use of this software.
// Permission is granted to anyone to use this software for any purpose,
// including commercial applications, and to alter it and redistribute it
// freely, subject to the following restrictions:
// 1. The origin of this software must not be misrepresented; you must not
//    claim that you wrote the original software. If you use this software
//    in a product, an acknowledgment in the product documentation would be
//    appreciated but is not required.
// 2. Altered source versions must be plainly marked as such, and must not be
//    misrepresented as being the original software.
// 3. This notice may not be removed or altered from any source distribution.
//

#define _USE_MATH_DEFINES
#include <math.h>
#include <stdio.h>
#include "Recast.h"
#include "RecastAssert.h"

/// @par
///
/// Allows the formation of walkable regions that will flow over low lying 
/// objects such as curbs, and up structures such as stairways. 
/// 
/// Two neighboring spans are walkable if: <tt>rcAbs(currentSpan.smax - neighborSpan.smax) < waklableClimb</tt>
/// 
/// @warning Will override the effect of #rcFilterLedgeSpans.  So if both filters are used, call
/// #rcFilterLedgeSpans after calling this filter. 
///
/// @see rcHeightfield, rcConfig
/// 如果下面的span可走，上面的span不可走，并且两个span的max之差小于walkableClimb，则把上面的span也修改为可走
void rcFilterLowHangingWalkableObstacles(rcContext* ctx, const int walkableClimb, rcHeightfield& solid)
{
	rcAssert(ctx);

	rcScopedTimer timer(ctx, RC_TIMER_FILTER_LOW_OBSTACLES);
	
	const int w = solid.width;
	const int h = solid.height;
	
	for (int y = 0; y < h; ++y)
	{
		for (int x = 0; x < w; ++x)
		{
			rcSpan* ps = 0;
			bool previousWalkable = false;
			unsigned char previousArea = RC_NULL_AREA;
			
			for (rcSpan* s = solid.spans[x + y*w]; s; ps = s, s = s->next)
			{
				const bool walkable = s->area != RC_NULL_AREA;
				// If current span is not walkable, but there is walkable
				// span just below it, mark the span above it walkable too.
                // 上面的span不可走，下面的span可走
				if (!walkable && previousWalkable)
				{
                    // 上下span的上表面之差小于等于walkClimb
					if (rcAbs((int)s->smax - (int)ps->smax) <= walkableClimb)
						s->area = previousArea;
				}
				// Copy walkable flag so that it cannot propagate
				// past multiple non-walkable objects.
				previousWalkable = walkable;
				previousArea = s->area;
			}
		}
	}
}

/// @par
///
/// A ledge is a span with one or more neighbors whose maximum is further away than @p walkableClimb
/// from the current span's maximum.
/// This method removes the impact of the overestimation of conservative voxelization 
/// so the resulting mesh will not have regions hanging in the air over ledges.
/// 
/// A span is a ledge if: <tt>rcAbs(currentSpan.smax - neighborSpan.smax) > walkableClimb</tt>
/// 
/// @see rcHeightfield, rcConfig
void rcFilterLedgeSpans(rcContext* ctx, const int walkableHeight, const int walkableClimb,
						rcHeightfield& solid)
{
	rcAssert(ctx);
	
	rcScopedTimer timer(ctx, RC_TIMER_FILTER_BORDER);

	const int w = solid.width;
	const int h = solid.height;
	const int MAX_HEIGHT = 0xffff;
	
	// Mark border spans.
	for (int y = 0; y < h; ++y)
	{
		for (int x = 0; x < w; ++x)
		{
			for (rcSpan* s = solid.spans[x + y*w]; s; s = s->next)
			{
				// Skip non walkable spans.
				if (s->area == RC_NULL_AREA)
					continue;
				
				const int bot = (int)(s->smax);
				const int top = s->next ? (int)(s->next->smin) : MAX_HEIGHT;

				// 下面两种情况时，会认为当前span为不可行走,下面的遍历检查了以下两种情况
				// a：当nspan比span低walkableClimb以上时，说明span走向nspan时有落差，则span置位RC_NULL_AREA
				// b：当span的所有nspan之间的高度差相差walkableClimb以上时，则认为比较陡峭，span置位RC_NULL_AREA

				// Find neighbours minimum height.
				// a1
				int minh = MAX_HEIGHT;

				// Min and max height of accessible neighbours.
				// b1:nspan的最小bot和最大bot
				int asmin = s->smax;
				int asmax = s->smax;

				for (int dir = 0; dir < 4; ++dir)
				{
					int dx = x + rcGetDirOffsetX(dir);
					int dy = y + rcGetDirOffsetY(dir);
					// Skip neighbours which are out of bounds.
					// 过滤处于边界的格子
					if (dx < 0 || dy < 0 || dx >= w || dy >= h)
					{
						// a2:小于-walkableClimb即可
						minh = rcMin(minh, -walkableClimb - bot);
						continue;
					}

					// From minus infinity to the first span.
					rcSpan* ns = solid.spans[dx + dy*w];
					int nbot = -walkableClimb;
					int ntop = ns ? (int)ns->smin : MAX_HEIGHT;
					// Skip neightbour if the gap between the spans is too small.
					if (rcMin(top,ntop) - rcMax(bot,nbot) > walkableHeight)
						// a3
						minh = rcMin(minh, nbot - bot);
					
					// Rest of the spans.
					for (ns = solid.spans[dx + dy*w]; ns; ns = ns->next)
					{
						nbot = (int)ns->smax;
						ntop = ns->next ? (int)ns->next->smin : MAX_HEIGHT;
						// Skip neightbour if the gap between the spans is too small.
						if (rcMin(top,ntop) - rcMax(bot,nbot) > walkableHeight)
						{
							// a4
							minh = rcMin(minh, nbot - bot);
						
							// Find min/max accessible neighbour height.
							// b2:判断<= walkableClimb的情况即可，超过walkableClimb的由a判断
							if (rcAbs(nbot - bot) <= walkableClimb)
							{
								if (nbot < asmin) asmin = nbot;
								if (nbot > asmax) asmax = nbot;
							}
							
						}
					}
				}
				
				// The current span is close to a ledge if the drop to any
				// neighbour span is less than the walkableClimb.
				// a5
				if (minh < -walkableClimb)
				{
					s->area = RC_NULL_AREA;
				}
				// If the difference between all neighbours is too large,
				// we are at steep slope, mark the span as ledge.
				// b3
				else if ((asmax - asmin) > walkableClimb)
				{
					s->area = RC_NULL_AREA;
				}
			}
		}
	}
}

/// @par
///
/// For this filter, the clearance above the span is the distance from the span's 
/// maximum to the next higher span's minimum. (Same grid column.)
/// 
/// @see rcHeightfield, rcConfig
/// 两个span之间小于walkableHeight，则span不可行走
void rcFilterWalkableLowHeightSpans(rcContext* ctx, int walkableHeight, rcHeightfield& solid)
{
	rcAssert(ctx);
	
	rcScopedTimer timer(ctx, RC_TIMER_FILTER_WALKABLE);
	
	const int w = solid.width;
	const int h = solid.height;
	const int MAX_HEIGHT = 0xffff;
	
	// Remove walkable flag from spans which do not have enough
	// space above them for the agent to stand there.
	for (int y = 0; y < h; ++y)
	{
		for (int x = 0; x < w; ++x)
		{
			for (rcSpan* s = solid.spans[x + y*w]; s; s = s->next)
			{
				const int bot = (int)(s->smax);
				const int top = s->next ? (int)(s->next->smin) : MAX_HEIGHT;
				if ((top - bot) <= walkableHeight)
					s->area = RC_NULL_AREA;
			}
		}
	}
}

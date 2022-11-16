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
#include "RecastAlloc.h"
#include "RecastAssert.h"

inline bool overlapBounds(const float* amin, const float* amax, const float* bmin, const float* bmax)
{
	bool overlap = true;
	overlap = (amin[0] > bmax[0] || amax[0] < bmin[0]) ? false : overlap;
	overlap = (amin[1] > bmax[1] || amax[1] < bmin[1]) ? false : overlap;
	overlap = (amin[2] > bmax[2] || amax[2] < bmin[2]) ? false : overlap;
	return overlap;
}

inline bool overlapInterval(unsigned short amin, unsigned short amax,
							unsigned short bmin, unsigned short bmax)
{
	if (amax < bmin) return false;
	if (amin > bmax) return false;
	return true;
}


static rcSpan* allocSpan(rcHeightfield& hf)
{
	// If running out of memory, allocate new page and update the freelist.
	if (!hf.freelist || !hf.freelist->next)
	{
		// Create new page.
		// Allocate memory for the new pool.
		rcSpanPool* pool = (rcSpanPool*)rcAlloc(sizeof(rcSpanPool), RC_ALLOC_PERM);
		if (!pool) return 0;

		// Add the pool into the list of pools.
		pool->next = hf.pools;
		hf.pools = pool;
		// Add new items to the free list.
		rcSpan* freelist = hf.freelist;
		rcSpan* head = &pool->items[0];
		rcSpan* it = &pool->items[RC_SPANS_PER_POOL];
		do
		{
			--it;
			it->next = freelist;
			freelist = it;
		}
		while (it != head);
		hf.freelist = it;
	}
	
	// Pop item from in front of the free list.
	rcSpan* it = hf.freelist;
	hf.freelist = hf.freelist->next;
	return it;
}

static void freeSpan(rcHeightfield& hf, rcSpan* ptr)
{
	if (!ptr) return;
	// Add the node in front of the free list.
	ptr->next = hf.freelist;
	hf.freelist = ptr;
}

static bool addSpan(rcHeightfield& hf, const int x, const int y,
					const unsigned short smin, const unsigned short smax,
					const unsigned char area, const int flagMergeThr)
{
	
	int idx = x + y*hf.width;
	
	rcSpan* s = allocSpan(hf);
	if (!s)
		return false;
	s->smin = smin;
	s->smax = smax;
	s->area = area;
	s->next = 0;
	
	// Empty cell, add the first span.
	if (!hf.spans[idx])
	{
		hf.spans[idx] = s;
		return true;
	}
	rcSpan* prev = 0;
	rcSpan* cur = hf.spans[idx];
	
	// Insert and merge spans.
	while (cur)
	{
        // s在cur下面
		if (cur->smin > s->smax)
		{
			// Current span is further than the new span, break.
			break;
		}
        // s在cur上面
		else if (cur->smax < s->smin)
		{
			// Current span is before the new span advance.
			prev = cur;
			cur = cur->next;
		}
        // 重叠了
		else
		{
			// Merge spans.
            // 合并smin和smax
            if (cur->smin < s->smin)
				s->smin = cur->smin;
			if (cur->smax > s->smax)
				s->smax = cur->smax;
			
			// Merge flags.
            // 合并area标志，如果一个span比另一个span高出walkableClimb，则可行走
            if (rcAbs((int)s->smax - (int)cur->smax) <= flagMergeThr)
				s->area = rcMax(s->area, cur->area);
			
			// Remove current span.
			rcSpan* next = cur->next;
			freeSpan(hf, cur);
			if (prev)
				prev->next = next;
			else
				hf.spans[idx] = next;
            // 可能s跨越多个span，所以继续遍历
            cur = next;
		}
	}
	
	// Insert new span.
	if (prev)
	{
		s->next = prev->next;
		prev->next = s;
	}
	else
	{
		s->next = hf.spans[idx];
		hf.spans[idx] = s;
	}

	return true;
}

/// @par
///
/// The span addition can be set to favor flags. If the span is merged to
/// another span and the new @p smax is within @p flagMergeThr units
/// from the existing span, the span flags are merged.
///
/// @see rcHeightfield, rcSpan.
bool rcAddSpan(rcContext* ctx, rcHeightfield& hf, const int x, const int y,
			   const unsigned short smin, const unsigned short smax,
			   const unsigned char area, const int flagMergeThr)
{
	rcAssert(ctx);

	if (!addSpan(hf, x, y, smin, smax, area, flagMergeThr))
	{
		ctx->log(RC_LOG_ERROR, "rcAddSpan: Out of memory.");
		return false;
	}

	return true;
}

// divides a convex polygons into two convex polygons on both sides of a line
static void dividePoly(const float* in, int nin,
					  float* out1, int* nout1,
					  float* out2, int* nout2,
					  float x, int axis)
{
    // 最多产生7边形，为什么数组大小为12？？？？？
	float d[12];
    // 放入输入点到切割线的距离，d[n]为x到点的距离距离,注意下面是x 【-】 in[i*3+axis]，所以d[n]>0在【左】，d[n]<0在【右】
    for (int i = 0; i < nin; ++i)
		d[i] = x - in[i*3+axis];

    // m为【左】多边形点的索引，n为【右】多边形点的索引
    int m = 0, n = 0;
    // 遍历所有的边与切割线的相交关系，i和j两个点即为一条边
    for (int i = 0, j = nin-1; i < nin; j=i, ++i)
	{
        // 上一个点是否切割线【左】方向，第一个点的上一个点为最后一个点
        bool ina = d[j] >= 0;
        // 当前点是否在切割线【左】
        bool inb = d[i] >= 0;
        // 如果i j在切割线两边，则新产生一个顶点，即切割点，切割点属于被切开的两个多边形，所以out1和out2中都要加入此切割点
        if (ina != inb)
		{
            // s为切割线线把i和j分割的比例，j占i+j的比例，(d[j] - d[i])=j到i的距离
            float s = d[j] / (d[j] - d[i]);
            // 切割点的三维坐标，根据距离比例算出来
            out1[m*3+0] = in[j*3+0] + (in[i*3+0] - in[j*3+0])*s;
			out1[m*3+1] = in[j*3+1] + (in[i*3+1] - in[j*3+1])*s;
			out1[m*3+2] = in[j*3+2] + (in[i*3+2] - in[j*3+2])*s;
            // 新产生的切割点，要放在两个多边形里
            rcVcopy(out2 + n*3, out1 + m*3);
			m++;
			n++;
			// add the i'th point to the right polygon. Do NOT add points that are on the dividing line
			// since these were already added above
            // 当前点在【左】，把d[i]对应的点放入【左】多边形
            if (d[i] > 0)
			{
				rcVcopy(out1 + m*3, in + i*3);
				m++;
			}
            // 当前点在【右】，把d[i]对应的点放入【右】多边形
            else if (d[i] < 0)
			{
				rcVcopy(out2 + n*3, in + i*3);
				n++;
			}
		}
		else // same side
		{
			// add the i'th point to the right polygon. Addition is done even for points on the dividing line
			if (d[i] >= 0)
			{
				rcVcopy(out1 + m*3, in + i*3);
				m++;
				if (d[i] != 0)
					continue;
			}
			rcVcopy(out2 + n*3, in + i*3);
			n++;
		}
	}

	*nout1 = m;
	*nout2 = n;
}



static bool rasterizeTri(const float* v0, const float* v1, const float* v2,
						 const unsigned char area, rcHeightfield& hf,
						 const float* bmin, const float* bmax,
						 const float cs, const float ics, const float ich,
						 const int flagMergeThr)
{
	const int w = hf.width;
	const int h = hf.height;
	float tmin[3], tmax[3];
	const float by = bmax[1] - bmin[1];
	
	// Calculate the bounding box of the triangle.
	rcVcopy(tmin, v0);
	rcVcopy(tmax, v0);
	rcVmin(tmin, v1);
	rcVmin(tmin, v2);
	rcVmax(tmax, v1);
	rcVmax(tmax, v2);
	
	// If the triangle does not touch the bbox of the heightfield, skip the triagle.
	if (!overlapBounds(bmin, bmax, tmin, tmax))
		return true;
	
	// Calculate the footprint of the triangle on the grid's y-axis
    // 先不考虑y轴，把三角形平铺在xz面上，y0，y1位二维平面上 以cs为单位的高度
	int y0 = (int)((tmin[2] - bmin[2])*ics);
	int y1 = (int)((tmax[2] - bmin[2])*ics);
	y0 = rcClamp(y0, 0, h-1);
	y1 = rcClamp(y1, 0, h-1);
	
	// Clip the triangle into all grid cells it touches.
    // 申请一块7*3*4个float长度的内存，其实是为了内存连续的性能优化
    // 4的意义:下面的in inrow p1 p2四份等长数据，这些数据里存的是多边形，即顶点坐标
    // 3的意义:存的是顶点，所以3个float， x y z
    // 7的意义:对三角形切割时，切出来的一个格子，最多可变成一个7边形
	float buf[7*3*4];
	float *in = buf, *inrow = buf+7*3, *p1 = inrow+7*3, *p2 = p1+7*3;

	rcVcopy(&in[0], v0);
	rcVcopy(&in[1*3], v1);
	rcVcopy(&in[2*3], v2);
    // 初始为三角形，所以定点数为3
	int nvrow, nvIn = 3;

    // y轴上从低到高切割
	for (int y = y0; y <= y1; ++y)
	{
		// Clip polygon to row. Store the remaining polygon as well
		const float cz = bmin[2] + y*cs;
        // 多边形切割，按照z轴cz+cs切割，inrow p1为切割后的多边形，其中inrow为位于切割线下面的多边形，p1为切割线上线的多边形
        dividePoly(in, nvIn, inrow, &nvrow, p1, &nvIn, cz+cs, 2);
        // inrow为切割后的一般，p1为切割后的另一半，inrow在本次循环内按x0到x1切割完成，另一半p1下次循环在进行切分
        // 所以p1和in交换下 下次再切分in即p1
		rcSwap(in, p1);
        // 这次要处理的这一半多边形没切到东西，可能切到了in（多边形）的一个顶点或者与y轴平行的一条边，顶点和边没必要体素化，所以continue
        if (nvrow < 3) continue;
		
		// find the horizontal bounds in the row
		float minX = inrow[0], maxX = inrow[0];
        // 遍历inrow多边形的顶点，找到最小x和最大x
		for (int i=1; i<nvrow; ++i)
		{
			if (minX > inrow[i*3])	minX = inrow[i*3];
			if (maxX < inrow[i*3])	maxX = inrow[i*3];
		}
		int x0 = (int)((minX - bmin[0])*ics);
		int x1 = (int)((maxX - bmin[0])*ics);
		x0 = rcClamp(x0, 0, w-1);
		x1 = rcClamp(x1, 0, w-1);

		int nv, nv2 = nvrow;

        // x轴上从左到右切割
		for (int x = x0; x <= x1; ++x)
		{
			// Clip polygon to column. store the remaining polygon as well
			const float cx = bmin[0] + x*cs;
            // 看到传入的参数有点懵，上面的第一次调用没注意
            // 仔细看p1 p2，这两个位置的形参一直被当做空数组，原来返回切割后的两个多边形，上面已经把in和p1兑换，此时p1实际为in，in的实际内存空间当成空数组p1重用
            // nv2用来告诉dividePoly方法inrow的长度，&nv &nv2作用是返回参数，&nv2被修改后作为下一次遍历inrow的长度nv2
			dividePoly(inrow, nv2, p1, &nv, p2, &nv2, cx+cs, 0);
            // p1为切割线左边的多边形，p2为切割线右边的多边形，此时p1已经被切割完毕（已经是一个格子内的多边形了）
            // p2还没切割完成，与inrow交换，下次遍历切割
			rcSwap(inrow, p2);
            // p1没切出多边形，则不进行下面的体素处理
			if (nv < 3) continue;
			
			// Calculate min and max of the span.
            // 多边形p1的最低高度，最高高度
			float smin = p1[1], smax = p1[1];
			for (int i = 1; i < nv; ++i)
			{
				smin = rcMin(smin, p1[i*3+1]);
				smax = rcMax(smax, p1[i*3+1]);
			}
            // 包围盒的最低高度和最高高度
			smin -= bmin[1];
			smax -= bmin[1];
			// Skip the span if it is outside the heightfield bbox
			if (smax < 0.0f) continue;
			if (smin > by) continue;
			// Clamp the span to the heightfield bbox.
			if (smin < 0.0f) smin = 0;
			if (smax > by) smax = by;
			
			// Snap the span to the heightfield height grid.
            // 包围盒最低体素，最高体素
			unsigned short ismin = (unsigned short)rcClamp((int)floorf(smin * ich), 0, RC_SPAN_MAX_HEIGHT);
			unsigned short ismax = (unsigned short)rcClamp((int)ceilf(smax * ich), (int)ismin+1, RC_SPAN_MAX_HEIGHT);
			
			if (!addSpan(hf, x, y, ismin, ismax, area, flagMergeThr))
				return false;
		}
	}

	return true;
}

/// @par
///
/// No spans will be added if the triangle does not overlap the heightfield grid.
///
/// @see rcHeightfield
bool rcRasterizeTriangle(rcContext* ctx, const float* v0, const float* v1, const float* v2,
						 const unsigned char area, rcHeightfield& solid,
						 const int flagMergeThr)
{
	rcAssert(ctx);

	rcScopedTimer timer(ctx, RC_TIMER_RASTERIZE_TRIANGLES);

	const float ics = 1.0f/solid.cs;
	const float ich = 1.0f/solid.ch;
	if (!rasterizeTri(v0, v1, v2, area, solid, solid.bmin, solid.bmax, solid.cs, ics, ich, flagMergeThr))
	{
		ctx->log(RC_LOG_ERROR, "rcRasterizeTriangle: Out of memory.");
		return false;
	}

	return true;
}

/// @par
///
/// Spans will only be added for triangles that overlap the heightfield grid.
///
/// @see rcHeightfield
bool rcRasterizeTriangles(rcContext* ctx, const float* verts, const int /*nv*/,
						  const int* tris, const unsigned char* areas, const int nt,
						  rcHeightfield& solid, const int flagMergeThr)
{
	rcAssert(ctx);

	rcScopedTimer timer(ctx, RC_TIMER_RASTERIZE_TRIANGLES);
	
	const float ics = 1.0f/solid.cs;
	const float ich = 1.0f/solid.ch;
	// Rasterize triangles.
	for (int i = 0; i < nt; ++i)
	{
		const float* v0 = &verts[tris[i*3+0]*3];
		const float* v1 = &verts[tris[i*3+1]*3];
		const float* v2 = &verts[tris[i*3+2]*3];
		// Rasterize.
		if (!rasterizeTri(v0, v1, v2, areas[i], solid, solid.bmin, solid.bmax, solid.cs, ics, ich, flagMergeThr))
		{
			ctx->log(RC_LOG_ERROR, "rcRasterizeTriangles: Out of memory.");
			return false;
		}
	}

	return true;
}

/// @par
///
/// Spans will only be added for triangles that overlap the heightfield grid.
///
/// @see rcHeightfield
bool rcRasterizeTriangles(rcContext* ctx, const float* verts, const int /*nv*/,
						  const unsigned short* tris, const unsigned char* areas, const int nt,
						  rcHeightfield& solid, const int flagMergeThr)
{
	rcAssert(ctx);

	rcScopedTimer timer(ctx, RC_TIMER_RASTERIZE_TRIANGLES);
	
	const float ics = 1.0f/solid.cs;
	const float ich = 1.0f/solid.ch;
	// Rasterize triangles.
	for (int i = 0; i < nt; ++i)
	{
		const float* v0 = &verts[tris[i*3+0]*3];
		const float* v1 = &verts[tris[i*3+1]*3];
		const float* v2 = &verts[tris[i*3+2]*3];
		// Rasterize.
		if (!rasterizeTri(v0, v1, v2, areas[i], solid, solid.bmin, solid.bmax, solid.cs, ics, ich, flagMergeThr))
		{
			ctx->log(RC_LOG_ERROR, "rcRasterizeTriangles: Out of memory.");
			return false;
		}
	}

	return true;
}

/// @par
///
/// Spans will only be added for triangles that overlap the heightfield grid.
///
/// @see rcHeightfield
bool rcRasterizeTriangles(rcContext* ctx, const float* verts, const unsigned char* areas, const int nt,
						  rcHeightfield& solid, const int flagMergeThr)
{
	rcAssert(ctx);
	
	rcScopedTimer timer(ctx, RC_TIMER_RASTERIZE_TRIANGLES);
	
	const float ics = 1.0f/solid.cs;
	const float ich = 1.0f/solid.ch;
	// Rasterize triangles.
	for (int i = 0; i < nt; ++i)
	{
		const float* v0 = &verts[(i*3+0)*3];
		const float* v1 = &verts[(i*3+1)*3];
		const float* v2 = &verts[(i*3+2)*3];
		// Rasterize.
		if (!rasterizeTri(v0, v1, v2, areas[i], solid, solid.bmin, solid.bmax, solid.cs, ics, ich, flagMergeThr))
		{
			ctx->log(RC_LOG_ERROR, "rcRasterizeTriangles: Out of memory.");
			return false;
		}
	}

	return true;
}

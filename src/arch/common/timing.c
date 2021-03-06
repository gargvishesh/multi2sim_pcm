/*
 *  Multi2Sim
 *  Copyright (C) 2012  Rafael Ubal (ubal@ece.neu.edu)
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received as copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include <lib/esim/esim.h>
#include <lib/mhandle/mhandle.h>
#include <lib/util/debug.h>
#include <lib/util/timer.h>
#include <math.h>

#include "arch.h"
#include "emu.h"
#include "timing.h"
#include "mem-system/cache.c"

extern unsigned short *mem_lines_wear_dist;
extern unsigned long long global_delay_due_to_flushing;

extern unsigned long long totalDiffWords;
extern unsigned long long totalDiffBytes;
extern unsigned long long totalDiffBits;

extern const int MEM_LINES_COUNT;

extern int cache_flush_dram_dirty();

/*
 * Class 'Timing'
 */


CLASS_IMPLEMENTATION(Timing);


void TimingCreate(Timing *self)
{
	/* Virtual functions */
	asObject(self)->Dump = TimingDump;
	self->Run = TimingRun;
	self->MemConfigDefault = TimingMemConfigDefault;
	self->MemConfigCheck = TimingMemConfigCheck;
	self->MemConfigParseEntry = TimingMemConfigParseEntry;
}


void TimingDestroy(Timing *self)
{
}


void TimingDump(Object *self, FILE *f)
{
}


void TimingDumpSummary(Timing *self, FILE *f)
{
	double time_in_sec;
	double cycles_per_sec;
	double cycle_time;  /* In nanoseconds */

	struct arch_t *arch;

	Emu *emu;
	Timing *timing;

	/* Obtain objects */
	timing = asTiming(self);
	arch = timing->arch;
	assert(arch);
	emu = arch->emu;
	assert(emu);

	/* Calculate statistics */
	time_in_sec = (double) m2s_timer_get_value(emu->timer) / 1.0e6;
	cycles_per_sec = time_in_sec > 0.0 ? (double) timing->cycle / time_in_sec : 0.0;
	cycle_time = (double) esim_domain_cycle_time(timing->frequency_domain) / 1000.0;
        cache_flush_dram_dirty();

	/* Print */
	fprintf(f, "SimTime = %.2f [ns]\n", timing->cycle * cycle_time);
	fprintf(f, "Frequency = %d [MHz]\n", timing->frequency);
	fprintf(f, "Cycles = %lld\n", timing->cycle + global_delay_due_to_flushing);
	fprintf(f, "CyclesPerSecond = %.0f\n", cycles_per_sec);
        

        double squareSum = 0, sum = 0;
        long long maxWrites = 0;
        int i;
        fprintf(stderr, "Page_Wise_Wear_Distribution: ");
        for (i = 0; i < MEM_LINES_COUNT; i++) {
        /************/
        //fprintf(f, "Addr:%d %d\n", i, mem_lines_wear_dist[i]);
        //mem_lines_wear_dist[i] = i;
        /***********/
        fprintf(stderr, "%u ", mem_lines_wear_dist[i]);
        if (mem_lines_wear_dist[i] > maxWrites) {
                maxWrites = mem_lines_wear_dist[i];
            }
            sum += mem_lines_wear_dist[i];
            squareSum += (mem_lines_wear_dist[i] * mem_lines_wear_dist[i]);
        }
        fprintf(stderr, "\n");
        
        double mean = (double)sum/(double)MEM_LINES_COUNT;
        double variance = (squareSum + (double)MEM_LINES_COUNT*(mean*mean) - 2*mean*sum)/(double)MEM_LINES_COUNT;
        fprintf(f, "Wear Distribution (Standard Deviation among Cache Line Writes) = %lf\n", sqrt(variance));
        fprintf(f, "Total Writes (Words) = %llu\n", totalDiffWords);
        fprintf(f, "Total Writes (Bytes) = %llu\n", totalDiffBytes);
        fprintf(f, "Total Writes (Bits) = %llu\n", totalDiffBits);
        fprintf(f, "Max Writes (In 4 Byte Words Per Cache Line) = %llu\n", maxWrites);
}


int TimingRun(Timing *self)
{
	panic("%s: abstract function not overridden",
			__FUNCTION__);
	return 0;
}


void TimingMemConfigDefault(Timing *self, struct config_t *config)
{
	panic("%s: abstract function not overridden",
			__FUNCTION__);
}


void TimingMemConfigCheck(Timing *self, struct config_t *config)
{
	panic("%s: abstract function not overridden",
			__FUNCTION__);
}


void TimingMemConfigParseEntry(Timing *self, struct config_t *config, char *section)
{
	panic("%s: abstract function not overridden",
			__FUNCTION__);
}

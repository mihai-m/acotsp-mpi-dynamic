/*

       AAAA    CCCC   OOOO   TTTTTT   SSSSS  PPPPP
      AA  AA  CC     OO  OO    TT    SS      PP  PP
      AAAAAA  CC     OO  OO    TT     SSSS   PPPPP
      AA  AA  CC     OO  OO    TT        SS  PP
      AA  AA   CCCC   OOOO     TT    SSSSS   PP

######################################################
##########    ACO algorithms for the TSP    ##########
######################################################

      Version: 1.0
      File:    main.c
      Author:  Thomas Stuetzle
      Purpose: main routines and control for the ACO algorithms
      Check:   README and gpl.txt
      Copyright (C) 2002  Thomas Stuetzle
*/

/***************************************************************************

    Program's name: acotsp

    Ant Colony Optimization algorithms (AS, ACS, EAS, RAS, MMAS, BWAS) for the 
    symmetric TSP 

    Copyright (C) 2004  Thomas Stuetzle

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    email: stuetzle no@spam ulb.ac.be
    mail address: Universite libre de Bruxelles
                  IRIDIA, CP 194/6
                  Av. F. Roosevelt 50
                  B-1050 Brussels
		  Belgium

***************************************************************************/


#include <stdio.h>
#include <math.h>
#include <limits.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#include <mpi.h>
#include <conio.h>

#include "ants.h"
#include "utilities.h"
#include "InOut.h"
#include "TSP.h"
#include "timer.h"
#include "ls.h"


#define INTERVAL_UPDATE 30 //procesele comunica cu Master la fiecare INERVAL_UPDATE iteratii
#define INTERVAL_MOD 120 //instanta se modifica la fiecare INTERVAL_MOD iteratii

void swap_long(long *a, long *b)
{
	long t = *a;
	*a = *b;
	*b = t;
}

void swap_double(double *a, double *b)
{
	double t = *a;
	*a = *b;
	*b = t;
}


long int termination_condition( void )
/*    
      FUNCTION:       checks whether termination condition is met 
      INPUT:          none
      OUTPUT:         0 if condition is not met, number neq 0 otherwise
      (SIDE)EFFECTS:  none
*/
{
  return ( ((n_tours >= max_tours) && (elapsed_time( VIRTUAL ) >= max_time)) || 
	  (best_so_far_ant->tour_length <= optimal)); 
}



void construct_solutions( void )
/*    
      FUNCTION:       manage the solution construction phase
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  when finished, all ants of the colony have constructed a solution  
*/
{
    long int k;        /* counter variable */
    long int step;    /* counter of the number of construction steps */

    TRACE ( printf("construct solutions for all ants\n"); );

    /* Mark all cities as unvisited */
    for ( k = 0 ; k < n_ants ; k++) {
	ant_empty_memory( &ant[k] );
    }
    
    step = 0; 
    /* Place the ants on same initial city */
    for ( k = 0 ; k < n_ants ; k++ )
	place_ant( &ant[k], step);

    while ( step < n-1 ) {
	step++;
	for ( k = 0 ; k < n_ants ; k++ ) {
	    neighbour_choose_and_move_to_next( &ant[k], step);
	    if ( acs_flag )
		local_acs_pheromone_update( &ant[k], step );
	}
    }

    step = n;
    for ( k = 0 ; k < n_ants ; k++ ) {
	ant[k].tour[n] = ant[k].tour[0];
	ant[k].tour_length = compute_tour_length( ant[k].tour );
	if ( acs_flag )
	    local_acs_pheromone_update( &ant[k], step );
    }
    n_tours += n_ants;
}



void init_try( long int ntry ) 
/*    
      FUNCTION: initilialize variables appropriately when starting a trial
      INPUT:    trial number
      OUTPUT:   none
      COMMENTS: none
*/
{

    TRACE ( printf("INITIALIZE TRIAL\n"); );
  
    start_timers();
    time_used = elapsed_time( VIRTUAL );
    time_passed = time_used;

    if (comp_report) {
        fprintf(comp_report,"seed %ld\n",seed);
        fflush(comp_report);
    }
    /* Initialize variables concerning statistics etc. */
  
    n_tours      = 1;
    iteration    = 1;
    restart_iteration = 1;
    lambda       = 0.05;            
    best_so_far_ant->tour_length = INFTY;
    found_best   = 0;
  
    /* Initialize the Pheromone trails, only if ACS is used, pheromones
       have to be initialized differently */
    if ( !(acs_flag || mmas_flag || bwas_flag) ) {
	trail_0 = 1. / ( (rho) * nn_tour() );
	/* in the original papers on Ant System, Elitist Ant System, and
	   Rank-based Ant System it is not exactly defined what the
	   initial value of the pheromones is. Here we set it to some
	   small constant, analogously as done in MAX-MIN Ant System.  
	*/
	init_pheromone_trails( trail_0 );
    } 
    if ( bwas_flag ) {
	trail_0 = 1. / ( (double) n * (double) nn_tour()) ;
	init_pheromone_trails( trail_0 );
    } 
    if ( mmas_flag ) {
	trail_max = 1. / ( (rho) * nn_tour() );
	trail_min = trail_max / ( 2. * n );
	init_pheromone_trails( trail_max );   
    }
    if ( acs_flag ) {
	trail_0 = 1. / ( (double) n * (double) nn_tour( ) ) ;
	init_pheromone_trails( trail_0 );
    }
  
    /* Calculate combined information pheromone times heuristic information */
    compute_total_information();
    
    if (comp_report) fprintf(comp_report,"begin try %li \n",ntry);
    if (stat_report) fprintf(stat_report,"begin try %li \n",ntry);
}



void local_search( void )
/*    
      FUNCTION:       manage the local search phase; apply local search to ALL ants; in 
                      dependence of ls_flag one of 2-opt, 2.5-opt, and 3-opt local search
		      is chosen.
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  all ants of the colony have locally optimal tours
      COMMENTS:       typically, best performance is obtained by applying local search 
                      to all ants. It is known that some improvements (e.g. convergence 
		      speed towards high quality solutions) may be obtained for some 
		      ACO algorithms by applying local search to only some of the ants.
		      Overall best performance is typcially obtained by using 3-opt.
*/
{
    long int k;

    TRACE ( printf("apply local search to all ants\n"); );

    for ( k = 0 ; k < n_ants ; k++ ) {
	switch (ls_flag) {
        case 1:
	    two_opt_first( ant[k].tour );    /* 2-opt local search */
            break;
        case 2:
	    two_h_opt_first( ant[k].tour );  /* 2.5-opt local search */
            break;
        case 3:
	    three_opt_first( ant[k].tour );  /* 3-opt local search */
            break;
        default:
	    fprintf(stderr,"type of local search procedure not correctly specified\n");
	    exit(1);
	}
	ant[k].tour_length = compute_tour_length( ant[k].tour );
        if (termination_condition()) return;
    }
}



void update_statistics( void )
/*    
      FUNCTION:       manage some statistical information about the trial, especially
                      if a new best solution (best-so-far or restart-best) is found and
                      adjust some parameters if a new best solution is found
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  restart-best and best-so-far ant may be updated; trail_min 
                      and trail_max used by MMAS may be updated
*/
{

    long int iteration_best_ant;
    double p_x; /* only used by MMAS */

    iteration_best_ant = find_best(); /* iteration_best_ant is a global variable */

    if ( ant[iteration_best_ant].tour_length < best_so_far_ant->tour_length ) {

	time_used = elapsed_time( VIRTUAL ); /* best sol found after time_used */
	copy_from_to( &ant[iteration_best_ant], best_so_far_ant );
	copy_from_to( &ant[iteration_best_ant], restart_best_ant );

	found_best = iteration;
	restart_found_best = iteration;
	found_branching = node_branching(lambda);
	branching_factor = found_branching;
	if ( mmas_flag ) {
	    if ( !ls_flag ) {
		p_x = exp(log(0.05)/n); 
		trail_min = 1. * (1. - p_x) / (p_x * (double)((nn_ants + 1) / 2));
		trail_max = 1. / ( (rho) * best_so_far_ant->tour_length );
		trail_0 = trail_max;
		trail_min = trail_max * trail_min; 
	    } else {
		trail_max = 1. / ( (rho) * best_so_far_ant->tour_length );
		trail_min = trail_max / ( 2. * n );
		trail_0 = trail_max;
	    }
	}
	write_report();
    }
    if ( ant[iteration_best_ant].tour_length < restart_best_ant->tour_length ) {
	copy_from_to( &ant[iteration_best_ant], restart_best_ant );
	restart_found_best = iteration;
	if (myid==0)
		printf("restart best: %ld, restart_found_best %ld, time %.2f\n",restart_best_ant->tour_length, restart_found_best, elapsed_time ( VIRTUAL ));
    }
}



void search_control_and_statistics( void )
/*    
      FUNCTION:       occasionally compute some statistics and check whether algorithm 
                      is converged 
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  restart-best and best-so-far ant may be updated; trail_min 
                      and trail_max used by MMAS may be updated
*/
{
    TRACE ( printf("SEARCH CONTROL AND STATISTICS\n"); );

    if (!(iteration % 100)) {
	population_statistics();
	branching_factor = node_branching(lambda);
	if (myid==0)
	printf("\nbest so far %ld, iteration: %ld, time %.2f, b_fac %.5f\n",best_so_far_ant->tour_length,iteration,elapsed_time( VIRTUAL),branching_factor);

	if ( mmas_flag && (branching_factor < branch_fac) && (iteration - restart_found_best > 250) ) {
	    /* MAX-MIN Ant System was the first ACO algorithm to use
	       pheromone trail re-initialisation as implemented
	       here. Other ACO algorithms may also profit from this mechanism.
	    */
		if (myid==0)
	    printf("INIT TRAILS!!!\n"); restart_best_ant->tour_length = INFTY; 
	    init_pheromone_trails( trail_max );
	    compute_total_information();
	    restart_iteration = iteration;
	    restart_time = elapsed_time( VIRTUAL );
	}
	if (myid==0)
	printf("try %li, iteration %li, b-fac %f \n\n", n_try,iteration,branching_factor);
    }
}



void as_update( void )
/*    
      FUNCTION:       manage global pheromone deposit for Ant System
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  all ants deposit pheromones on matrix "pheromone"
*/
{
    long int   k;

    TRACE ( printf("Ant System pheromone deposit\n"); );

    for ( k = 0 ; k < n_ants ; k++ )
		global_update_pheromone( &ant[k] );
	if (iteration > INTERVAL_UPDATE + size)
		global_update_pheromone( best_so_far_ant ); // o fi ok?
}



void eas_update( void )
/*    
      FUNCTION:       manage global pheromone deposit for Elitist Ant System
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  all ants plus elitist ant deposit pheromones on matrix "pheromone"
*/
{
    long int   k;

    TRACE ( printf("Elitist Ant System pheromone deposit\n"); );

    for ( k = 0 ; k < n_ants ; k++ )
	global_update_pheromone( &ant[k] );
    global_update_pheromone_weighted( best_so_far_ant, elitist_ants );
}



void ras_update( void )
/*    
      FUNCTION:       manage global pheromone deposit for Rank-based Ant System
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  the ras_ranks-1 best ants plus the best-so-far ant deposit pheromone 
                      on matrix "pheromone"
      COMMENTS:       this procedure could be implemented slightly faster, but it is 
                      anyway not critical w.r.t. CPU time given that ras_ranks is 
		      typically very small.
*/
{
    long int i, k, b, target;
    long int *help_b;

    TRACE ( printf("Rank-based Ant System pheromone deposit\n"); );

    help_b = malloc( n_ants  * sizeof(long int) );
    for ( k = 0 ; k < n_ants ; k++ )
	help_b[k] = ant[k].tour_length;

    for ( i = 0 ; i < ras_ranks-1 ; i++ ) {
	b = help_b[0]; target = 0;
	for ( k = 0 ; k < n_ants ; k++ ) {
	    if ( help_b[k] < b ) {
		b = help_b[k]; target = k;
	    }
	}
	help_b[target] = LONG_MAX;
	global_update_pheromone_weighted( &ant[target], ras_ranks-i-1 );
    }
    global_update_pheromone_weighted( best_so_far_ant, ras_ranks );
    free ( help_b );
}



void mmas_update( void )
/*    
      FUNCTION:       manage global pheromone deposit for MAX-MIN Ant System
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  either the iteration-best or the best-so-far ant deposit pheromone 
                      on matrix "pheromone"
*/
{
    /* we use default upper pheromone trail limit for MMAS and hence we
       do not have to worry regarding keeping the upper limit */

    long int iteration_best_ant;

    TRACE ( printf("MAX-MIN Ant System pheromone deposit\n"); );

    if ( iteration % u_gb ) {
	iteration_best_ant = find_best();
	global_update_pheromone( &ant[iteration_best_ant] );
    }
    else {
        if ( u_gb == 1 && (iteration - restart_found_best > 50))
	    global_update_pheromone( best_so_far_ant );
        else 
	    global_update_pheromone( restart_best_ant );
    }

    if ( ls_flag ) {
	/* implement the schedule for u_gb as defined in the 
	   Future Generation Computer Systems article or in Stuetzle's PhD thesis.
	   This schedule is only applied if local search is used.
	*/
	if ( ( iteration - restart_iteration ) < 25 )
	    u_gb = 25;
	else if ( (iteration - restart_iteration) < 75 )
	    u_gb = 5;
	else if ( (iteration - restart_iteration) < 125 )
	    u_gb = 3;
	else if ( (iteration - restart_iteration) < 250 )
	    u_gb = 2;
	else 
	    u_gb = 1;
    } else
	u_gb = 25;
  
}



void bwas_update( void )
/*    
      FUNCTION:       manage global pheromone deposit for Best-Worst Ant System
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  either the iteration-best or the best-so-far ant deposit pheromone 
                      on matrix "pheromone"
*/
{
    long int   iteration_worst_ant, distance_best_worst;

    TRACE ( printf("Best-worst Ant System pheromone deposit\n"); );

    global_update_pheromone( best_so_far_ant );
    iteration_worst_ant = find_worst();
    bwas_worst_ant_update( &ant[iteration_worst_ant], best_so_far_ant );
    distance_best_worst = distance_between_ants( best_so_far_ant, &ant[iteration_worst_ant]);
/*    printf("distance_best_worst %ld, tour length worst %ld\n",distance_best_worst,ant[iteration_worst_ant].tour_length); */
    if ( distance_best_worst < (long int) (0.05 * (double) n) ) {
	restart_best_ant->tour_length = INFTY;
	init_pheromone_trails( trail_0 );
	restart_iteration = iteration;    
	restart_time = elapsed_time( VIRTUAL );
	if (myid==0)
	printf("init pheromone trails with %.15f, iteration %ld\n",trail_0,iteration);
    }
    else 
	bwas_pheromone_mutation();
}



void acs_global_update( void )
/*    
      FUNCTION:       manage global pheromone deposit for Ant Colony System
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  the best-so-far ant deposits pheromone on matrix "pheromone"
      COMMENTS:       global pheromone deposit in ACS is done per default using 
                      the best-so-far ant; Gambardella & Dorigo examined also iteration-best
		      update (see their IEEE Trans. on Evolutionary Computation article), 
		      but did not use it for the published computational results.
*/
{
    TRACE ( printf("Ant colony System global pheromone deposit\n"); );

    global_acs_pheromone_update( best_so_far_ant );
}



void pheromone_trail_update( void )  
/*    
      FUNCTION:       manage global pheromone trail update for the ACO algorithms
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  pheromone trails are evaporated and pheromones are deposited 
                      according to the rules defined by the various ACO algorithms.
*/
{
    /* Simulate the pheromone evaporation of all pheromones; this is not necessary 
       for ACS (see also ACO Book) */
    if ( as_flag || eas_flag || ras_flag || bwas_flag || mmas_flag ) {
	if ( ls_flag ) {
	    if ( mmas_flag )
		mmas_evaporation_nn_list();
	    else
		evaporation_nn_list();
	    /* evaporate only pheromones on arcs of candidate list to make the 
	       pheromone evaporation faster for being able to tackle large TSP 
	       instances. For MMAS additionally check lower pheromone trail limits.
	    */
	} else {
	    /* if no local search is used, evaporate all pheromone trails */
	    evaporation();
	}
    }

    /* Next, apply the pheromone deposit for the various ACO algorithms */
    if ( as_flag )
	as_update(); 
    else if ( eas_flag )
	eas_update();
    else if ( ras_flag )
	ras_update();
    else if ( mmas_flag )
	mmas_update();
    else if ( bwas_flag )
	bwas_update();
    else if ( acs_flag )
	acs_global_update();

  /* check pheromone trail limits for MMAS; not necessary if local
     search is used, because in the local search case lower pheromone trail
     limits are checked in procedure mmas_evaporation_nn_list */
    if ( mmas_flag && !ls_flag )
	check_pheromone_trail_limits();

  /* Compute combined information pheromone times heuristic info after
     the pheromone update for all ACO algorithms except ACS; in the ACS case 
     this is already done in the pheromone update procedures of ACS */
    if ( as_flag || eas_flag || ras_flag || mmas_flag || bwas_flag ) {
	if ( ls_flag ) {
	    compute_nn_list_total_information();
	} else {
	    compute_total_information();
	}
    }
}



/* --- main program ------------------------------------------------------ */

int main(int argc, char *argv[]) {
/*    
      FUNCTION:       main control for running the ACO algorithms
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  none
      COMMENTS:       this function controls the run of "max_tries" independent trials

*/

    long int i;

	// mpi variables
		//int myid, size;  //mutate in "InOut.h"
		int tag = 80;
		//MPI_Status status;

		//variabilele din MPI_Recv
		long lung_p;
		long* tour_p; //vector
		int proces;
		MPI_Status Stat;

		//if (myid==0) {
			//pastrate de Master
			long lung_top10[10];
			double time_top10[10];
			long* tour_top10[10]; //matrix
			int nr_solutii_top10 = 0; //numarul de solutii din top10
		//}

		FILE **procReport = NULL; //vector -> file streams
		char tempstr[100];  //numele fisierului txt

		long int j,k,h; //counters
		double dval; //double variable for general use
		long int new_seed; //un nou seed pentru functia ran01
	/////

	// dynamicity variables
		long minDimX, maxDimX, minDimY, maxDimY;
		double dim_instanta_x, dim_instanta_y; //dimensiunea instantei
		// ^ adica diferenta dintre cel mai mare si cel mai mic x, respectiv y
		double razaTeleport;

		double xNP, yNP; //coordonatele noului punct
		double distNP; //distanta fata de vechiul punct
	/////

	myReport = fopen("myReport.txt", "w");  //declarat in "InOut.h"

	MPI_Init(&argc, &argv);
	MPI_Comm_rank(MPI_COMM_WORLD, &myid);
	MPI_Comm_size(MPI_COMM_WORLD, &size);

	//aloc memorie vectorului de stream-uri
	procReport = (FILE *)malloc(size * sizeof(FILE));
	//deschid un fisier text separat pentru fiecare proces
	sprintf(tempstr,"procReport[%d].txt",myid);
	procReport[myid] = fopen(tempstr, "w");

	start_timers();

    init_program(argc, argv);

    instance.nn_list = compute_nn_lists();
    pheromone = generate_double_matrix( n, n );
    total = generate_double_matrix( n, n );

    time_used = elapsed_time( VIRTUAL );
	if (myid==0)
		printf("Initialization took %.10f seconds\n",time_used);

	//aloc memorie celorlalti vectori:  (calloc?)
	if (myid==0)
		tour_p = (long *)malloc((instance.n+1) * sizeof(long));
		for (i=0;i<10;++i) {
			tour_top10[i] = (long *)malloc((instance.n+1) * sizeof(long));
			lung_top10[i] = INFTY;
			time_top10[i] = -1.0;
		}

	new_seed = seed;

	n_try = myid;
	init_try(n_try);

	//aflu dimensiunea tablei
	minDimX = maxDimX = minDimY = maxDimY = 0; //minDim si maxDim sunt indecsi
	for (i=1;i<instance.n;++i) {
		if (instance.nodeptr[minDimX].x > instance.nodeptr[i].x)
			minDimX = i;
		if (instance.nodeptr[maxDimX].x < instance.nodeptr[i].x)
			maxDimX = i;
		if (instance.nodeptr[minDimY].y > instance.nodeptr[i].y)
			minDimY = i;
		if (instance.nodeptr[maxDimY].y < instance.nodeptr[i].y)
			maxDimY = i;
	}
	dim_instanta_x = instance.nodeptr[maxDimX].x - instance.nodeptr[minDimX].x;
	dim_instanta_y = instance.nodeptr[maxDimY].y - instance.nodeptr[minDimY].y;
	// ^ am aflat dimensiunea tablei
	// in functie de asta, voi alege raza cercului pentru TSP dinamic:
	razaTeleport = (double)(dim_instanta_x + dim_instanta_y) / 2 / 10;

	fprintf(myReport,"minDimX = %g maxDimX = %g\nminDimY = %g, maxDimY = %g\n",
			instance.nodeptr[minDimX].x,instance.nodeptr[maxDimX].x,
			instance.nodeptr[minDimY].y,instance.nodeptr[maxDimY].y);
	fprintf(myReport,"dim_instanta_x = %g\ndim_instanta_y = %g\n",dim_instanta_x,dim_instanta_y);
	fprintf(myReport,"razaTeleport = %g\n\n",razaTeleport);

	// o data la cateva iteratii, voi alege aleatoriu un nod
	// care va fi mutat intr-un punct ales aleator pe suprafata cercului
	// cu centrul in nod si cu raza razaTeleport.


	while ( !termination_condition() ) {

		if (iteration % INTERVAL_MOD == 0) { //modific instanta
			if (myid==0) {
				k = (long)(ran01(&new_seed) * (double)instance.n); //aleg la intamplare un nod
				fprintf(myReport,"\n\nbefore: nod %d, x=%g, y=%g",k,instance.nodeptr[k].x,instance.nodeptr[k].y);
				do {
					do {
						xNP = 2 * razaTeleport * ran01(&new_seed) - razaTeleport;
						yNP = 2 * razaTeleport * ran01(&new_seed) - razaTeleport;
					} while(sqrt(xNP*xNP + yNP*yNP) > razaTeleport || sqrt(xNP*xNP + yNP*yNP) < razaTeleport/3 );
					xNP = instance.nodeptr[k].x + xNP;
					yNP = instance.nodeptr[k].y + yNP;
				} while(xNP < instance.nodeptr[minDimX].x || xNP > instance.nodeptr[maxDimX].x || 
						yNP < instance.nodeptr[minDimY].y || yNP > instance.nodeptr[maxDimY].y);
				distNP = sqrt(pow(xNP-instance.nodeptr[k].x, 2) + pow(yNP-instance.nodeptr[k].y, 2));
				fprintf(myReport,"\nafter: nod %d, x=%g, y=%g, d=%g\n",k,xNP,yNP,distNP);
				//acum tot ce tre' sa fac e sa trimit xNP, yNP si k sclavilor
				//iar fiecare sclav isi va face singur actualizarea instantei
				//(ca sa nu ma mai complic cu pack/unpack sau crearea unor noi tipuri de date MPI)
			}

			//la sfarsit trimit instanta modificata sclavilor (bcast)
			//MPI_Bcast(&k, 1, MPI_INT, 0, MPI_COMM_WORLD);
			//MPI_Bcast(&xNP, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
			//MPI_Bcast(&yNP, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);

			instance.nodeptr[k].x = xNP;
			instance.nodeptr[k].y = yNP;
			// ^ am mutat nodul

			for (i=0;i<instance.n;++i) { //actualizez matricea distantelor
				//distance(i, k) poate fi diferita de distance(k, i)
				instance.distance[i][k] = distance(i, k);
				instance.distance[k][i] = distance(k, i);
			}

			instance.nn_list = compute_nn_lists();
			//sa modific matricea pheromone?

			fflush(myReport);

			//recalculez top10
			if (myid==0) {
				nr_solutii_top10 = 0;
				for (k=0;k<10;++k)
					if (lung_top10[k] == INFTY)
						break;
					else
						lung_top10[k] = compute_tour_length(tour_top10[k]);
				//apoi sortez top10 (fiindca la modificarea instantei se poate schiba ordinea)
				//bubblesort e suficient
				for (i=0;i<k-1;++i)
					for (j=i+1;j<k;++j)
						if (lung_top10[i] > lung_top10[j]) {
							swap_long(&lung_top10[i], &lung_top10[j]);
							swap_double(&time_top10[i], &time_top10[j]);
							for (h=0;h<=instance.n;++h)
								swap_long(&tour_top10[i][h], &tour_top10[j][h]);
						}
			}
			//dupa ce modific instanta, trebuie recalculata si cea mai buna furnica:
			best_so_far_ant->tour_length = compute_tour_length( best_so_far_ant->tour );
			restart_best_ant->tour_length = compute_tour_length( restart_best_ant->tour );
		}

		construct_solutions();

		if ( ls_flag > 0 )
			local_search();

		update_statistics();

		pheromone_trail_update();

		search_control_and_statistics();

		if (iteration % INTERVAL_UPDATE == myid && iteration >= INTERVAL_UPDATE) {
			if (myid==0) {
				//Master isi pune cea mai buna furnica in top10
				lung_p = best_so_far_ant->tour_length;
				tour_p = best_so_far_ant->tour; //pointeri
			}
			else {
				//fiecare proces trimite lui Master cea mai buna furnica:
				MPI_Send(&best_so_far_ant->tour_length, 1, MPI_LONG, 0, tag, MPI_COMM_WORLD);
				MPI_Send(best_so_far_ant->tour, instance.n+1, MPI_LONG, 0, tag, MPI_COMM_WORLD);
				//si asteapta ca raspuns cea mai buna solutie din top10
				MPI_Recv(&best_so_far_ant->tour_length, 1, MPI_LONG, 0, tag, MPI_COMM_WORLD, &Stat);
				MPI_Recv(best_so_far_ant->tour, instance.n+1, MPI_LONG, 0, tag, MPI_COMM_WORLD, &Stat);

				fprintf(procReport[myid],"PROCESS #%d @ iteration %d received lung_top10[0] = %d\n",myid,iteration,best_so_far_ant->tour_length);
				fflush(procReport[myid]);
			}
		}

		if (iteration % INTERVAL_UPDATE < size && myid==0 && iteration >= INTERVAL_UPDATE) {
			//primesc solutiile de la sclavi
			proces = 0; //iteration % INTERVAL_UPDATE;
			/*
			if (proces != 0) {
				MPI_Recv(&lung_p, 1, MPI_LONG, proces, tag, MPI_COMM_WORLD, &Stat);
				MPI_Recv(tour_p, instance.n+1, MPI_LONG, proces, tag, MPI_COMM_WORLD, &Stat);
			}
			*/
			//introduc in tour_top_10 solutia primita:
			//1. determin pozitia [k] pe care trebuie introdusa solutia
			k = -1;
			for (j=0;j<10;++j) {
				if (lung_p == lung_top10[j])
					break; //o solutie de aceasta lungime deja exista in tour_top10
				else if (lung_p < lung_top10[j]) {
					k = j;
					break;
				}
			}
			//2. daca solutia e suficient de buna pentru top10
			if (k != -1) {
				if (nr_solutii_top10 < 10)
					++nr_solutii_top10;
				//introduc solutia in tour_top10[k] dupa ce le cobor pe celelalte
				for (j=9;j>k;--j) {
					time_top10[j] = time_top10[j-1];
					lung_top10[j] = lung_top10[j-1];
					for (h=0;h<=instance.n;++h)
						tour_top10[j][h] = tour_top10[j-1][h];
				}
				time_top10[k] = elapsed_time( VIRTUAL );
				lung_top10[k] = lung_p;
				for (h=0;h<=instance.n;++h)
					tour_top10[k][h] = tour_p[h];
			}
			//acum am cele mai bune solutii sortate in tour_top10

			//trimit sclavilor cea mai buna solutie
			h = 0;

			// in caz ca vreau sa trimit o alta solutie...
			//new_seed = new_seed * (i+3) + i; //pregatesc o samanta noua pentru functia ran01
			//h = (int) (ran01( &new_seed ) * (double) nr_solutii_top10); /* random number between 0 .. nr_solutii_top10 - 1 */

			if (proces != 0) {/*
				MPI_Send(&lung_top10[h], 1, MPI_LONG, proces, tag, MPI_COMM_WORLD);
				MPI_Send(tour_top10[h], instance.n+1, MPI_LONG, proces, tag, MPI_COMM_WORLD);
				if (proces == 1) {
					fprintf(procReport[myid],"PROCESS #1 @ iteration %d received lung_top10[%d] = %d\n",iteration,h,lung_top10[h]);
					fflush(procReport[myid]);
				}*/
			}
			else {
				best_so_far_ant->tour_length = lung_top10[h];
				for (i=0;i<=instance.n;++i)
					best_so_far_ant->tour[i] = tour_top10[h][i];
				fprintf(procReport[myid],"PROCESS #0 @ iteration %d received lung_top10[%d] = %d\n",iteration,h,lung_top10[h]);
				fflush(procReport[myid]);
			}
		} //end if (iteration % INTERVAL_UPDATE < size && myid==0)

		if (iteration % INTERVAL_UPDATE == size && myid==0) {
			//AFISARE TOP_10
			fprintf(myReport,"\n\n=== TOP 10 @ iteration %d ===",iteration);
			for (i=0;i<10;++i) {
				if (lung_top10[i] == INFTY)
					break;
				fprintf(myReport,"\nlung_top10[%d] = %d  -  in %g seconds",i,lung_top10[i],time_top10[i]);
			}
			//fprintf(myReport,"\n");
			//for (j=0;j<=instance.n;++j)
			//	fprintf(myReport,"best_tour[%d] = %d\n",j,tour_top10[0][j]);
			/*
			h=0; j=0; dval=0;
			for (i=0;i<3;++i)
				if (lung_top10[i]!=INFTY) {
					h += lung_top10[i];
					dval += time_top10[i];
					++j;
				}
			if (j)
				fprintf(myReport,"\ntop3 average = %d      top3 time average = %g", h/j, dval/j);
			h=0; j=0; dval=0;
			for (i=0;i<10;++i)
				if (lung_top10[i]!=INFTY) {
					h += lung_top10[i];
					dval += time_top10[i];
					++j;
				}
			if (j)
				fprintf(myReport,"\ntop10 average = %d     top10 time average = %g", h/j, dval/j);
			*/
			fprintf(myReport,"\n#%d - time taken = %f", myid,elapsed_time( VIRTUAL ));
			//fprintf(myReport,"\n#%d - iterations used = %d", myid, iteration);
			fflush(myReport);
			//end AFISARE TOP_10
		} //end if (iteration % INTERVAL_UPDATE == size && myid==0)

		iteration++;

	} //end while ( !termination_condition() )




	if (myid==0) { //niste afisari in myReport.txt
		fprintf(myReport,"\n\n\n=== TOP 10 ===\n");
		for (i=0;i<10;++i)
			fprintf(myReport,"\nlung_top10[%d] = %d  -  in %g seconds",i,lung_top10[i],time_top10[i]);
		fprintf(myReport,"\n\n");
		//for (j=0;j<=instance.n;++j)
		//	fprintf(myReport,"best_tour[%d] = %d\n",j,tour_top10[0][j]);

		h=0; j=0; dval=0;
		for (i=0;i<3;++i)
			if (lung_top10[i]!=INFTY) {
				h += lung_top10[i];
				dval += time_top10[i];
				++j;
			}
		if (j)
			fprintf(myReport,"\ntop3 average = %d      top3 time average = %g", h/j, dval/j);
		h=0; j=0; dval=0;
		for (i=0;i<10;++i)
			if (lung_top10[i]!=INFTY) {
				h += lung_top10[i];
				dval += time_top10[i];
				++j;
			}
		if (j)
			fprintf(myReport,"\ntop10 average = %d     top10 time average = %g\n", h/j, dval/j);

		fprintf(myReport,"\n#%d - time taken = %f", myid,elapsed_time( VIRTUAL ));
		fprintf(myReport,"\n#%d - iterations used = %d", myid, iteration);
		fflush(myReport);
	}
	fprintf(procReport[myid],"\n#%d time taken = %f",myid,elapsed_time( VIRTUAL ));
	fprintf(procReport[myid],"\n#%d iterations used = %d",myid,iteration);
	fflush(procReport[myid]);
	exit_try(n_try);

	//output_solution(); //scrie in stat.lin318
    exit_program();
	if (myid==0) {
		printf("\n\ntime taken = %lf",elapsed_time( VIRTUAL ));
		printf("\niterations used = %ld",iteration);
		printf("\n\noverall best solution = %ld\n",lung_top10[0]);
	}

	/*
	if (myid==0) {
		for (i=0;i<10;++i)
			free(tour_top10[i]);
		//free(tour_p);
	}
	*/

    free( instance.distance );
    free( instance.nn_list );
    free( pheromone );
    free( total );
    free( best_in_try );
    free( best_found_at );
    free( time_best_found );
    free( time_total_run );
    for ( i = 0 ; i < n_ants ; i++ ) {
	free( ant[i].tour );
	free( ant[i].visited );
    }
    free( ant );
    free( best_so_far_ant->tour );
    free( best_so_far_ant->visited );
    free( prob_of_selection );

	MPI_Finalize();

    return(0);
}



//sa pastrez si un top10 pentru restart_best_ant ?

/*
  best_found_at[ntry] = found_best;
  time_best_found[ntry] = time_used;
  time_total_run[ntry] = elapsed_time( VIRTUAL );

  printf("Tour length = %ld\n\n",compute_tour_length( t ));
*/

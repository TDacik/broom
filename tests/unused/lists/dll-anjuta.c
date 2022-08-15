// use -m32
//based on:

/* Created by Anjuta version 0.1.7 */
/*	This file will not be overwritten */

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>


typedef int T;

//
// conventional dbly link representaion
//
struct dlistNode {
	T elm;
	struct dlistNode *next;
	struct dlistNode *prev;
};

typedef struct dlistNode *pdlistNode;
//

//glbls for conventional
pdlistNode pdHead, pdEnd;

//conventional
pdlistNode dNextNode ( pdlistNode pdNode)
{

	return (pdNode->next );
}

pdlistNode dPrevNode ( pdlistNode pdNode)
{

	return (pdNode->prev );
}

// conventional list delete
void ddelList()
{
	pdlistNode pdCurrent, pdNext;
	pdCurrent = pdHead;
	while (pdCurrent) {
		pdNext = dNextNode(pdCurrent);
		free(pdCurrent);
		pdCurrent = pdNext;
	}
}
	

// * for conventional insertAfter()
void dinsertAfter(pdlistNode pdNew, T theElm )
{
	pdlistNode pdPrev, pdCurrent, pdNext;
	pdCurrent= pdHead;
	
	while (pdCurrent) {
		pdNext = dNextNode(pdCurrent);
		if (pdCurrent->elm == theElm ) {
			if (pdNext ) {//fix the existing next node
				pdNext->prev = pdNew;
			}
			//fix the current node
			pdCurrent->next = pdNew;
			//fix the new node
			pdNew->next = pdNext;
			pdNew->prev = pdCurrent;
			break;
		}
		pdCurrent = pdNext;
	}
}

// conventional forward traversal
void dtraversefw( pdlistNode pdHead )
{
	//
	pdlistNode pCurrent;
	pCurrent = pdHead; 
	while (pCurrent) 
	{
		
		//printf(" -> %d\n", pCurrent->elm) ;
		pCurrent = dNextNode(pCurrent);

		
	}
}
// conventional backward traversal
void dtraversebw( pdlistNode pdHead )
{
	//
	pdlistNode pCurrent;
	pCurrent = pdHead; 
	while (pCurrent) 
	{
		//printf(" -> %d\n", pCurrent->elm) ;
		pCurrent = dPrevNode(pCurrent);
	}
}

//conventional insert	
void dinsert ( T elm)
{
	pdlistNode pdnewNode = (pdlistNode)malloc(sizeof(struct dlistNode) );
	if (! pdnewNode) return;
	pdnewNode->elm = elm;
	pdnewNode->next = pdnewNode->prev = NULL;
	
	//brand new
	if ( !pdHead ) {
		pdHead = pdEnd = pdnewNode;
	}else {
		dinsertAfter(pdnewNode, pdEnd->elm );
		pdEnd = pdnewNode;
	}
	return ;	
}

#define NO_OF_ITEM_IN_LIST		30000

// exercise the conventional struct
void exerciseDlist()
{

	int  i;

	printf("Before conventional insert()\n" );
	for (i = 0; i < NO_OF_ITEM_IN_LIST; i++)
		dinsert ( (T) i );
	printf("After conventional insert()\n" );

	printf ("Total Memory taken by conventional structure = %lu bytes.\n", NO_OF_ITEM_IN_LIST *sizeof(struct dlistNode) );
	
	//forward
	printf("Before conventioal  dtraversefw(pdHead )\n" );
	dtraversefw(pdHead );
	printf("After conventioal  dtraversefw(pdHead )\n" );
	
	//backward
	printf("Before conventioal dtraversebw(pdEnd)\n" );
	dtraversebw(pdEnd);
	printf("After conventioal dtraversebw(pdEnd)\n" );

	
	//delete
	printf("Before conventioal ddelList ()\n" );
	ddelList ();
	printf("After conventioal ddelList ()\n" );
}

int main()

{
	exerciseDlist();


	return (0);
}



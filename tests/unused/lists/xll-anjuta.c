// use -m32
// based on:

/* Created by Anjuta version 0.1.7 */
/*	This file will not be overwritten */

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

// use a single ptr to traverse back and forth
// //////////////////////////////////////////////
// | 0   |   | 1  |  | 2   | |  3  | | 4   | | 5   |
// |-----|   |-----| |-----| |-----| |-----| |-----|
// |(1^0)|   |(2^0)| |(3^1)| |(4^2)| |(5^3)| |(4^0)|
//
// Numerator of a node is the element.
// (m^n) is the exclusive or of ptr to m, and ptr to n.
// pStart points to element 0, pEnd points to 5 in this example
//
//
// pStart = pEnd = NULL => list is empty
// pStart = pEnd <> NULL => list is singleton


typedef int T;

//
// dbly link represented by ptr distance
//
struct listNode{
	T elm;
	struct listNode * ptrdiff;
};

typedef struct listNode *plistNode;


//globls for ptrdiff ds
plistNode pStart, pEnd;


// * for ptrdiff
plistNode NextNode( plistNode pNode, plistNode pPrevNode)
{

	return ((plistNode) ((int) pNode->ptrdiff ^ ( int)pPrevNode) );
}


// ptr.dist list delete
void delList ()
{
	//
	plistNode pPrev, pCurrent;
	pPrev = NULL;
	pCurrent = pStart;
	
	while ( pCurrent ) {
		pCurrent->ptrdiff = NextNode( pCurrent, pPrev);
		if (pPrev)
			free(pPrev);
		if ( !pCurrent->ptrdiff ){
			printf(" Final node being deleted in prt.dist. =%d\n", pCurrent->elm);
			free(pCurrent);
			pCurrent = NULL;
			continue;
		}
		pPrev = pCurrent;
		pCurrent = pCurrent->ptrdiff;
	}
}
	
// for dist. ptr.
void insertAfter ( plistNode pNew, T theElm )
{
	plistNode pPrev, pCurrent, pNext;
	pPrev = NULL;
	pCurrent = pStart;
	
	while (pCurrent) {
		pNext =  NextNode(pCurrent, pPrev);
		if (pCurrent->elm == theElm ) {
			/*fw traversal is done */
			//
			if (pNext ) { // fix the existing next node
				pNext->ptrdiff = (plistNode) ((int)pNext->ptrdiff ^ ( int) pCurrent ^ (int)pNew );
			}
			//fix the current node
			pCurrent->ptrdiff = (plistNode) ((int)pNew ^  (int)pNext ^ (int)pCurrent->ptrdiff);
			//fix the new node
			pNew->ptrdiff = (plistNode) ( (int)pCurrent ^ (int)pNext );
			break;
		}
		pPrev = pCurrent;
		pCurrent = pNext;
	}
}

// ptr. dist. struct. traversal
void traverse( plistNode pRoot )
{
	//
	plistNode pCurrent, pPrev, pNext;

	pPrev = NULL;	
	pCurrent = pRoot; 

	while (pCurrent) 
	{
		//printf(" -> %d\n", pCurrent->elm) ;
		pNext = NextNode(pCurrent, pPrev );
		pPrev = pCurrent;
		pCurrent = pNext;
		
	}
}

// dist. ptr.  insertion
void insert( T elm)
{
	//
	plistNode pnewNode = (plistNode)malloc(sizeof(struct listNode) );
	if (! pnewNode) {
		printf(" malloc failed in insert( T elm) \n");
		return;
	}
	pnewNode->elm = elm;
	pnewNode->ptrdiff = NULL;
	
	//brand new
	if ( !pStart ) {
		pStart = pEnd = pnewNode;
		
	}else {
		insertAfter( pnewNode, pEnd->elm);
		pEnd = pnewNode;
	}
	return ;
	
}

#define NO_OF_ITEM_IN_LIST		30000


void exerciseDistptrlist()
{
	int i;

	printf("Before insert(prt.dist.)\n");
	// exercise the ptr distance structure
	for (i = 0; i < NO_OF_ITEM_IN_LIST ; i++)
		insert ( (T) i );
	printf( "After insert(prt.dist.)\n" );
		
	printf ("Total Memory taken by ptr distance structure = %lu bytes.\n", NO_OF_ITEM_IN_LIST *sizeof(struct listNode) );
	
	//forward traversal
	printf("Before traverse(pStart) of (prt.dist.)\n");
	traverse(pStart);
	printf( "After traverse(pStart) of(prt.dist.)\n");
	//backward traversal
	printf("Before traverse(pEnd) of (prt.dist.)\n");
	traverse(pEnd);
	printf( "After traverse(pEnd) of (prt.dist.)\n");

	//delete the whole list
	printf( "Before delList () of (prt.dist.)\n");
	delList ();
	printf("After delList () of (prt.dist.)\n");

}

int main()

{
	exerciseDistptrlist();

	return (0);
}



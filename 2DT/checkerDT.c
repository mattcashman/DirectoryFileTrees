/*--------------------------------------------------------------------*/
/* checkerDT.c                                                        */
/* Author:                                                            */
/*--------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "checkerDT.h"
#include "dynarray.h"
#include "path.h"



/* see checkerDT.h for specification */
boolean CheckerDT_Node_isValid(Node_T oNNode) {
   Node_T oNParent;
   Path_T oPNPath;
   Path_T oPPPath;

   /* Sample check: a NULL pointer is not a valid node */
   if(oNNode == NULL) {
      fprintf(stderr, "A node is a NULL pointer\n");
      return FALSE;
   }

   /* Sample check: parent's path must be the longest possible
      proper prefix of the node's path */
   oNParent = Node_getParent(oNNode);
   if(oNParent != NULL) {
      oPNPath = Node_getPath(oNNode);
      oPPPath = Node_getPath(oNParent);

      /* Checks that path to root is one shorter for parent than for 
         child */
      if(Path_getSharedPrefixDepth(oPNPath, oPPPath) !=
         Path_getDepth(oPNPath) - 1) {
         fprintf(stderr, "P-C nodes don't have P-C paths: (%s) (%s)\n",
                 Path_getPathname(oPPPath), Path_getPathname(oPNPath));
         return FALSE;
      }
   }
   return TRUE;
}

/*
   Performs a pre-order traversal of the tree rooted at oNNode.
   Returns FALSE if a broken invariant is found and
   returns TRUE otherwise.

   You may want to change this function's return type or
   parameter list to facilitate constructing your checks.
   If you do, you should update this function comment.
*/
static boolean CheckerDT_treeCheck(Node_T oNNode) {
   size_t ulIndex;
   
   if(oNNode!= NULL) {

      /* Sample check on each node: node must be valid */
      /* If not, pass that failure back up immediately */
      if(!CheckerDT_Node_isValid(oNNode))
         return FALSE;

      /* Recur on every child of oNNode */
      for(ulIndex = 0; ulIndex < Node_getNumChildren(oNNode); ulIndex++)
      {
         Node_T oNChild = NULL;
         int iStatus = Node_getChild(oNNode, ulIndex, &oNChild);

         if(iStatus != SUCCESS) {
            fprintf(stderr, "getNumChildren claims more children than getChild returns\n");
            return FALSE;
         }
         /* if recurring down one subtree results in a failed check
            farther down, passes the failure back up immediately */
         if(!CheckerDT_treeCheck(oNChild))
            return FALSE;
      }
   }
   return TRUE;
}

/* Internal function to check no two nodes have the same path. 
Returns FALSE if two nodes have the same absolute file path,
 otherwise returns TRUE */
static boolean CheckerDT_samePaths(Node_T oNNode, DynArray_T paths) {
   
   Path_T path;
   size_t i;

   if (oNNode == NULL) return TRUE;

   path = Node_getPath(oNNode);
   for (i = 0; i < DynArray_getLength(paths); i++) {
      if (Path_comparePath(path, DynArray_get(paths, i)) == 0) {
         fprintf(stderr, "Identical file paths not allowed: (%s)\n",
                 Path_getPathname(path));
         return FALSE;
      }
   }

   DynArray_add(paths, path);
   
   for (i = 0; i < Node_getNumChildren(oNNode); i++) {
      Node_T oNChild = NULL;
      int iStatus = Node_getChild(oNNode, i, &oNChild);
      if(iStatus != SUCCESS) {
         fprintf(stderr,
                 "getNumChildren claims more children than getChild returns\n");
         return FALSE;
      }
      if (!CheckerDT_samePaths(oNChild, paths)) {
         return FALSE;
      }
   }
   return TRUE;
}
   

/* see checkerDT.h for specification */
boolean CheckerDT_isValid(boolean bIsInitialized, Node_T oNRoot,
                          size_t ulCount) {
   DynArray_T paths = DynArray_new(0);


   /* Sample check on a top-level data structure invariant:
      if the DT is not initialized, its count should be 0. */
   if(!bIsInitialized)
      if(ulCount != 0) {
         fprintf(stderr, "Not initialized, but count is not 0\n");
         return FALSE;
      }

   /* Now checks invariants recursively at each node from the root. */
   if (!CheckerDT_treeCheck(oNRoot)) {
      return FALSE;
   }

   if (!CheckerDT_samePaths(oNRoot, paths)) {
         DynArray_free(paths);
         return FALSE;
   }
   DynArray_free(paths);

   return TRUE;
}

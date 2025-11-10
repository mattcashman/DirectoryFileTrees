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


/* Variable to check ulCount is accurate - measured number of nodes.
Incrimented in treeCheck and checked in main isValid function. */
static size_t nodeCount;


/* see checkerDT.h for specification */
boolean CheckerDT_Node_isValid(Node_T oNNode) {
   Node_T oNParent;
   Node_T oNChild;
   Path_T oPNPath;
   Path_T oPPPath;
   size_t numChildren;

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

   /* Check that getNumChildren is accurate */
   numChildren = Node_getNumChildren(oNNode);
   if (Node_getChild(oNNode, numChildren, &oNChild) == SUCCESS) {
      fprintf(stderr, "getNumChildren reports less children than getChild returns");
      return FALSE;
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
      nodeCount++;
      
      /* Sample check on each node: node must be valid */
      /* If not, pass that failure back up immediately */
      if(!CheckerDT_Node_isValid(oNNode))
         return FALSE;

      /* Check child nodes are in the right order */
      if (Node_getNumChildren(oNNode) >= 2) {
      for(ulIndex = 0;
          ulIndex < Node_getNumChildren(oNNode) - 1;
          ulIndex++) {
         Node_T oNCurrChild = NULL;
         Node_T oNNextChild = NULL;
         if (Node_getChild(oNNode, ulIndex, &oNCurrChild) != SUCCESS ||
             Node_getChild(oNNode, ulIndex+1, &oNNextChild) != SUCCESS)
         {
            fprintf(stderr, "getNumChildren claims more children than getChild returns\n");
            return FALSE;
               }
         if (Path_comparePath(Node_getPath(oNCurrChild),
                              Node_getPath(oNNextChild)) > 0) {
            fprintf(stderr, "Child nodes must be lexicographical order: (%s) and (%s)\n",
                    Path_getPathname(Node_getPath(oNCurrChild)),
                    Path_getPathname(Node_getPath(oNNextChild)));
            return FALSE;
         }
      }}

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

/* Internal function to check no two nodes in the tree with root oNNode
 have the same path. Returns FALSE if two nodes have the same absolute 
file path in the array paths, otherwise returns TRUE */
static boolean CheckerDT_samePaths(Node_T oNNode, DynArray_T paths) {
   /* path of the current node */   
   Path_T path;
   /* index counter */
   size_t i;

   /* Check node is worth checking */
   if (oNNode == NULL) return TRUE;

   /* get path to node, check against paths array */
   path = Node_getPath(oNNode);
   for (i = 0; i < DynArray_getLength(paths); i++) {
      if (Path_comparePath(path, DynArray_get(paths, i)) == 0) {
         fprintf(stderr, "Identical file paths not allowed: (%s)\n",
                 Path_getPathname(path));
         return FALSE;
      }
   }

   DynArray_add(paths, path);

   /* iterate test for identical paths for all child nodes */
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
   nodeCount = 0;

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

   if (nodeCount != ulCount) {
      fprintf(stderr,
              "Incorrect number of nodes reported in DT: (%ld) found but (%ld) reported\n",
              nodeCount, ulCount);
      return FALSE;
   }

   if (!CheckerDT_samePaths(oNRoot, paths)) {
         DynArray_free(paths);
         return FALSE;
   }
   DynArray_free(paths);

   return TRUE;
}

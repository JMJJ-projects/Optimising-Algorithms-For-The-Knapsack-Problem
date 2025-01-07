//John-Michael JENY JEYARAJ 12013787
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <limits.h>

// Fonction utilitaire pour obtenir le maximum de deux nombres.
int
max (int a, int b)
{
  return (a > b) ? a : b;
}

// Définition de la structure pour les objets.
typedef struct
{
  unsigned int weight;
  unsigned int value;
} Item;

// Variables globales pour l'algorithme de backtracking
// (ATTENTION: nous utilisons les variables globales dans cette version pour suivre le schéma vu en cours et en td)
Item *g_itmes;			// tableau d'objets
int g_n;			// nombre d'objets
int g_W;			// capacité du sac
int g_bestValue = 0;		// meilleure valeur trouvée jusqu'à présent
int g_currentValue = 0;		// valeur courante du sac
int g_currentWeight = 0;	// poids courant du sac
int profit_bound = 0;
// implémentation récursive de l'algorithme de backtracking

void
knapsackBT1 (int idx)
{
  // Si l'indice actuel est hors le tableau ou si le sac à dos est plein, mettre à jour bestValue si nécessaire
  if (idx == g_n || g_currentWeight == g_W)
    {
      g_bestValue = max (g_bestValue, g_currentValue);
      return;
    }

  // sauter l'objet courant
  knapsackBT1 (idx + 1);

  // Inclure l'objet actuel s'il ne dépasse pas la capacité du sac à dos
  if (g_currentWeight + g_itmes[idx].weight <= g_W)
    {
      // Mettre à jour currentWeight et currentValue avant l'appel récursif
      g_currentWeight += g_itmes[idx].weight;
      g_currentValue += g_itmes[idx].value;

      knapsackBT1 (idx + 1);

      // Annuler la décision d'inclure l'objet (backtracking)
      g_currentWeight -= g_itmes[idx].weight;
      g_currentValue -= g_itmes[idx].value;
    }
}

int
borneSomme (Item items[], int n, int W, int idx, int currentValue)
{
  int sup = currentValue;
  int currentWeight = 0;

  for (int i = idx; i < n; i++)
    {
      if (currentWeight + items[i].weight <= W)
	{
	  currentWeight += items[i].weight;
	  sup += items[i].value;
	}
      else
	{
	  int reste = W - currentWeight;
	  sup += items[i].value * reste / items[i].weight;
	  break;
	}
    }
  return sup;
}

// Algorithme de backtracking sans variables globales
int
knapsackBTUtil (Item items[], int n, int W, int idx, int currentValue,
		int *bestValue)
{
  if (idx == n || W == 0)
    {
      if (currentValue > *bestValue)
	*bestValue = currentValue;
      return *bestValue;
    }
  double borne = borneSomme (items, n, W, idx, currentValue);
  if (borne < *bestValue)
    return *bestValue;
  // Ne pas inclure l'objet idx
  knapsackBTUtil (items, n, W, idx + 1, currentValue, bestValue);

  // Inclure l'objet idx si le poids le permet
  if (items[idx].weight <= W)
    {
      knapsackBTUtil (items, n, W - items[idx].weight, idx + 1,
		      currentValue + items[idx].value, bestValue);
    }

  return *bestValue;
}

int
knapsackBT2 (Item items[], int n, int W)
{
  int bestValue = 0;
  return knapsackBTUtil (items, n, W, 0, 0, &bestValue);
}

// Fonction de programmation dynamique pour le problème du sac à dos 0/1.
int
knapsackDP (int W, Item items[], int n)
{
  int i, w;
  int **K = (int **) malloc ((n + 1) * sizeof (int *));
  for (i = 0; i <= n; i++)
    K[i] = (int *) malloc ((W + 1) * sizeof (int));

  for (i = 0; i <= n; i++)
    {
      for (w = 0; w <= W; w++)
	{
	  if (i == 0 || w == 0)
	    K[i][w] = 0;
	  else if (items[i - 1].weight <= w)
	    K[i][w] =
	      max (items[i - 1].value + K[i - 1][w - items[i - 1].weight],
		   K[i - 1][w]);
	  else
	    K[i][w] = K[i - 1][w];
	}
    }

  int result = K[n][W];
  for (i = 0; i <= n; i++)
    free (K[i]);
  free (K);
  return result;
}

int
knapsackDP_Value (int W, Item items[], int n)
{
  int V = items[0].value;
  for (int i = 1; i < n; i++)
    {
      V += items[i].value;
    }
  int dp[V + 1];
  dp[0] = 0;
  for (int j = 1; j < V; j++)
    dp[j] = INT_MAX;
  for (int i = 0; i < n; i++)
    {
      for (int v = V; v >= items[i].value; v--)
	{
	  if (dp[v - items[i].value] != INT_MAX)
	    {
	      if (dp[v] > items[i].weight + dp[v - items[i].value])
		dp[v] = items[i].weight + dp[v - items[i].value];
	    }
	}
    }
  for (int i = V; i > 0; i--)
    {
      if (dp[i] <= W)
	return i;
    }
  return 0;
}

int
knapsackDP_MinPoids (int W, int M, Item items[], int n)
{
  if (M == 0)
    return 0;
  int **dp = (int **) malloc ((n + 1) * sizeof (int *));
  for (int i = 0; i <= n; i++)
    {
      dp[i] = (int *) malloc ((W + 1) * sizeof (int));
    }

  // Remplir la table dp
  for (int i = 0; i <= n; i++)
    {
      for (int w = 0; w <= W; w++)
	{
	  if (i == 0 || w == 0)
	    {
	      dp[i][w] = 0;
	    }
	  else if (items[i - 1].weight <= w
		   && (dp[i - 1][w - items[i - 1].weight] +
		       items[i - 1].value) > dp[i - 1][w])
	    {
	      dp[i][w] =
		dp[i - 1][w - items[i - 1].weight] + items[i - 1].value;
	    }
	  else
	    {
	      dp[i][w] = dp[i - 1][w];
	    }
	}
    }

  // Trouver la valeur maximale avec le poids minimum M
  int maxValue = INT_MIN;
  for (int w = M; w <= W; w++)
    {
      if (dp[n][w] > maxValue)
	{
	  maxValue = dp[n][w];
	}
    }

  for (int i = 0; i <= n; i++)
    {
      free (dp[i]);
    }
  free (dp);

  return (maxValue == INT_MIN) ? 0 : maxValue;
}

void
swap (Item a, Item b)
{
  Item temp = a;
  a = b;
  b = temp;
}

int
partition (Item items[], int a, int b)
{
  int pivot = items[b].value / items[b].weight;
  int i = a - 1;

  for (int j = a; j <= b - 1; j++)
    {
      if (items[j].value / items[j].weight >= pivot)
	{
	  i++;
	  swap (items[i], items[j]);
	}
    }
  swap (items[i + 1], items[b]);
  return i + 1;
}

void
trirapide (Item items[], int a, int b)
{
  if (a < b)
    {
      int pi = partition (items, a, b);
      trirapide (items, a, pi - 1);
      trirapide (items, pi + 1, b);
    }
}

int
knapsack_Glouton (int W, Item items[], int n)
{
  trirapide (items, 0, n - 1);

  int total = 0;
  int currentWeight = 0;

  for (int i = 0; i < n; i++)
    {
      if (currentWeight + items[i].weight <= W)
	{
	  currentWeight += items[i].weight;
	  total += items[i].value;
	}
    }

  return total;
}

int
main ()
{
  FILE *fp = fopen ("instances.csv", "r");
  FILE *out = fopen ("average_times.csv", "w");
  FILE *sol = fopen ("solutions.csv", "w");
  if (!fp || !out || !sol)
    {
      printf ("Erreur lors de l'ouverture des fichiers.\n");
      return 1;
    }

  // Variables pour stocker les somme des temps et compter les instances par taille de problème
  double sumTimeBT1 = 0, sumTimeBT2 = 0, sumTimeDP = 0, sumTimeDP_V = 0, sumTimeDP_M = 0, sumTimeDP_G = 0;
  int count = 0, currentN = -1;

  char line[4096];
  while (fgets (line, 4096, fp))
    {
      int W, n, M;
      sscanf (line, "%d,%d,%d", &W, &n, &M);

      // Vérifcation si nous passons à une nouvelle taille de problème
      if (n != currentN)
	{
	  if (count > 0)
	    {
	      // Écrivez les moyennes pour la taille de problème précédente
	      fprintf (out, "%d, %f, %f, %f, %f, %f, %f\n",
		       currentN, sumTimeBT1 / count, sumTimeBT2 / count,
		       sumTimeDP / count, sumTimeDP_V / count,
		       sumTimeDP_M / count, sumTimeDP_G / count);
	    }
	  // Réinitialisez les compteurs pour la nouvelle taille
	  currentN = n;
	  sumTimeBT1 = sumTimeBT2 = sumTimeDP = sumTimeDP_V = sumTimeDP_M =
	    0, sumTimeDP_G = 0;
	  count = 0;
	}

      Item items[n];
      char *token = strtok (line, ",");
      token = strtok (NULL, ",");	// Passer le token W
      for (int i = 0; i < n && token != NULL; i++)
	{
	  token = strtok (NULL, ",");	// Passer le token n
	  sscanf (token, "%d", &items[i].weight);
	  token = strtok (NULL, ",");
	  sscanf (token, "%d", &items[i].value);
	}

      //La logique pour configurer et appeler vos fonctions de sac à dos.
      printf ("n=%d, W=%d M=%d\n", n, W, M);

      g_itmes = items;
      g_n = n;
      g_W = W;
      g_bestValue = 0;		// meilleure valeur trouvée jusqu'à présent
      g_currentValue = 0;	// valeur courante du sac
      g_currentWeight = 0;

      clock_t start = clock ();
      //knapsackBT1 (0);
      int maxValBT1 = g_bestValue;
      clock_t end = clock ();
      double timeBT1 = (double) (end - start) / CLOCKS_PER_SEC;
      sumTimeBT1 += timeBT1;

      start = clock ();
      int maxValBT2 = 0;	//int maxValBT2 = knapsackBT2 (items, n, W);
      end = clock ();
      double timeBT2 = (double) (end - start) / CLOCKS_PER_SEC;
      sumTimeBT2 += timeBT2;

      start = clock ();
      int maxValDP = knapsackDP (W, items, n);
      end = clock ();
      double timeDP = (double) (end - start) / CLOCKS_PER_SEC;
      sumTimeDP += timeDP;

      //knapsackDP_Value
      start = clock ();
      int maxValDP_V = knapsackDP_Value (W, items, n);
      end = clock ();
      double timeDP_V = (double) (end - start) / CLOCKS_PER_SEC;
      sumTimeDP_V += timeDP_V;

      //knapsackDP_MinPoids
      start = clock ();
      int maxValDP_M = knapsackDP_MinPoids (W, M, items, n);
      end = clock ();
      double timeDP_M = (double) (end - start) / CLOCKS_PER_SEC;
      sumTimeDP_M += timeDP_M;

      //Knapsack_Glouton
      start = clock ();
      int maxValDP_G = knapsack_Glouton (W, items, n);
      end = clock ();
      double timeDP_G = (double) (end - start) / CLOCKS_PER_SEC;
      sumTimeDP_G += timeDP_G;
      count++;

      fprintf (sol, "%d, %d, %f, %d, %f, %d, %f, %d, %d, %d, %d\n",
	       n, W, timeBT1, maxValBT1, timeBT2, maxValBT2, timeDP,
	       maxValDP, maxValDP_V, maxValDP_M, maxValDP_G);
    }

  // Les moyennes pour la dernière taille de problème
  if (count > 0)
    {
      fprintf (out, "%d, %f, %f, %f, %f, %f, %f\n",
	       currentN, sumTimeBT1 / count, sumTimeBT2 / count,
	       sumTimeDP / count, sumTimeDP_V / count, sumTimeDP_M / count,
	       sumTimeDP_G / count);
    }

  fclose (fp);
  fclose (out);
  return 0;
}

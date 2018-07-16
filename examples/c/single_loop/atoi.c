int _atoi(int *str, int n)
{
    int res = 0;

    for (int i = 0; i < n; i++)
        res = res * 10 + str[i];

    return res;
}

/*
  One auxiliary variable found :
  aux = aux * 10;

  Join found with the auxilary :

  aux = aux-l * aux-r
  res = res-l + aux-l * res-r

*/

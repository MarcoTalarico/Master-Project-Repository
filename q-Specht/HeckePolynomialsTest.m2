-- We will load the code for computing the Hecke Specht Polynomials;

------- Load the Package --------
restart
loadPackage "HeckeSpechtPolynomials"


------- Compute action of Hecke generators T_i as matrices --------


par = {3,1} -- Enter a partition
(R,hspList,MAT) = parToMat par;



------- Check if we do indeed have a basis -------

n = 3
field = frac(QQ[p])
R = field[x_1..x_n]

-- Caution: for n>4 may take a long time to compute all polynomials
hspSet := qSpechtPolynomial(p,R);
isBasis(flatten hspSet,R); 




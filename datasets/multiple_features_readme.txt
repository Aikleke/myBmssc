The multi-feature digit dataset
-------------------------------

Oowned and donated by:
----------------------

Robert P.W. Duin
Department of Applied Physics 
Delft University of Technology 
P.O. Box 5046, 2600 GA Delft
The Netherlands

email: duin@ph.tn.tudelft.nl
http : //www.ph.tn.tudelft.nl/~duin
tel +31 15 2786143

Usage
-----
A slightly different version of the database is used in

M. van Breukelen, R.P.W. Duin, D.M.J. Tax, and J.E. den Hartog, Handwritten
     digit recognition by combined classifiers, Kybernetika, vol. 34, no. 4,
     1998, 381-386.

M. van Breukelen and R.P.W. Duin, Neural Network Initialization by Combined
     Classifiers, in: A.K. Jain, S. Venkatesh, B.C. Lovell (eds.), ICPR'98,
     Proc. 14th Int. Conference on Pattern Recognition (Brisbane, Aug. 16-20),

The database as it is is used in:

A.K. Jain, R.P.W. Duin, J. Mao, Statisitcal Pattern Recognition: A Review,
     in preparation

Description
-----------

This dataset consists of features of handwritten numerals (`0'--`9')
extracted from a collection of Dutch utility maps. 200 patterns per
class (for a total of 2,000 patterns) have been digitized in  binary
images. These digits are represented in terms of the following six
feature sets (files): 

1. mfeat-fou: 76 Fourier coefficients of the character shapes; 
2. mfeat-fac: 216 profile correlations; 
3. mfeat-kar: 64 Karhunen-Love coefficients; 
4. mfeat-pix: 240 pixel averages in 2 x 3 windows; 
5. mfeat-zer: 47 Zernike moments; 
6. mfeat-mor: 6 morphological features. 

In each file the 2000 patterns are stored in ASCI on 2000 lines. The
first 200 patterns are of class `0', followed by sets of 200 patterns
for each of the classes `1' - `9'. Corresponding patterns in different
feature sets (files) correspond to the same original character.

The source image dataset is lost. Using the pixel-dataset (mfeat-pix)
sampled versions of the original images may be obtained (15 x 16 pixels).

Total number of instances:
--------------------------
2000 (200 instances per class)

Total number of attributes:
---------------------------
649 (distributed over 6 datasets,see above)

no missing attributes

Total number of classes:
------------------------
10

Format:
------
6 files, see above.
Each file contains 2000 lines, one for each instance.
Attributes are SPACE separated and can be loaded by Matlab as
> load filename
No missing attributes. Some are integer, others are real.



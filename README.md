# mfi - translate LaTeX typeset math expressions to OWL facts.


mfi (mathematically formulated information) is a Clojure library to translate a string representing
a LaTeX mathematical expression to OWL facts. 

## Motivation and Approach

Mathematical models of manufacturing production processes and operations can be
verified more easily when the models can be traced to supporting literature and published models.
As described in [1], engineering notebooks deployed as [Jupyter notebooks](http://jupyter.org) support
this mode of operation. The mfi Clojure library plays a small role in this effort by translating
LaTeX mathematical expression to OWL facts based on a small number of base concepts. Given the
general nature of the problem, mfi may have uses outside manufacturing analysis.

## Installation

1. Download the [leiningen shell script](http://leiningen.org/).
2. Type 'lein deps' at a shell prompt in the mfi directory and wait while it downloads all the related libraries. 
3. Type 'lein repl' at a shell prompt in the facility directory and waiting for a clojure prompt.
4. (tryme "$ x = 1$")

## Disclaimer
The use of any software or hardware by the project does not imply a recommendation or endorsement by NIST.

The use of the project results in other software or hardware products does not imply a recommendation or endorsement by NIST of those products.

We would appreciate acknowledgement if any of the project results are used, however, the use of the NIST logo is not allowed.

NIST-developed software is provided by NIST as a public service. You may use, copy and distribute copies of the software in any medium, provided that you keep intact this entire notice. You may improve, modify and create derivative works of the software or any portion of the software, and you may copy and distribute such modifications or works. Modified works should carry a notice stating that you changed the software and should note the date and nature of any such change. Please explicitly acknowledge the National Institute of Standards and Technology as the source of the software.

NIST-developed software is expressly provided “AS IS.” NIST MAKES NO WARRANTY OF ANY KIND, EXPRESS, IMPLIED, IN FACT OR ARISING BY OPERATION OF LAW, INCLUDING, WITHOUT LIMITATION, THE IMPLIED WARRANTY OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, NON-INFRINGEMENT AND DATA ACCURACY. NIST NEITHER REPRESENTS NOR WARRANTS THAT THE OPERATION OF THE SOFTWARE WILL BE UNINTERRUPTED OR ERROR-FREE, OR THAT ANY DEFECTS WILL BE CORRECTED. NIST DOES NOT WARRANT OR MAKE ANY REPRESENTATIONS REGARDING THE USE OF THE SOFTWARE OR THE RESULTS THEREOF, INCLUDING BUT NOT LIMITED TO THE CORRECTNESS, ACCURACY, RELIABILITY, OR USEFULNESS OF THE SOFTWARE.

You are solely responsible for determining the appropriateness of using and distributing the software and you assume all risks associated with its use, including but not limited to the risks and costs of program errors, compliance with applicable laws, damage to or loss of data, programs or equipment, and the unavailability or interruption of operation. This software is not intended to be used in any situation where a failure could cause risk of injury or damage to property. The software developed by NIST employees is not subject to copyright protection within the United States.

## Credits

Peter Denno 

April Nellis 


## References

[1]: [Denno, P.; Kim, D. B., "Integrating views of properties in models of unit manufacturing processes"," International Journal of Computer Integrated Manufacturing Vol, 20, Issue 9, 2016."](https://www.tandfonline.com/doi/full/10.1080/0951192X.2015.1130259?scroll=top&needAccess=true)

# Contact Us

<a target="_blank" href="mailto:peter.denno@nist.gov">Peter Denno (peter.denno ( at ) nist.gov</a>









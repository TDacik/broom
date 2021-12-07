# Copyright (C) Broom team
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

.PHONY: build doc clean examples

build:
	dune build src/broom.exe src/test.exe

doc: build
	dune build @doc
	[ -e doc ] || ln -sf _build/default/_doc/_html doc

examples:
	./scripts/run-examples

clean:
	rm -rf _build doc

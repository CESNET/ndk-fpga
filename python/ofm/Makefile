.PHONY: rpm

rpm: comp
	mkdir -p RPMBUILD/SOURCES
	/usr/bin/env python3 setup.py sdist
	cp dist/*.tar.gz RPMBUILD/SOURCES
	rpmbuild -ba package/ofm.spec --define "_topdir `pwd`/RPMBUILD"

comp:
	ln -s ../../comp comp

clean:
	rm comp -f
	rm -rf build dist *.egg-info
	rm -rf RPMBUILD

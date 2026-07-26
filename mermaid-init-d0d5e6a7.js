// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

(() => {
    const darkThemes = ['ayu', 'navy', 'coal'];
    const lightThemes = ['light', 'rust'];

    const classList = document.getElementsByTagName('html')[0].classList;

    let lastThemeWasLight = true;
    for (const cssClass of classList) {
        if (darkThemes.includes(cssClass)) {
            lastThemeWasLight = false;
            break;
        }
    }

    const theme = lastThemeWasLight ? 'default' : 'dark';
    // securityLevel 'loose' enables `click` directives and anchors in labels
    // (all diagram content is repo-authored). Diagram text uses the book's
    // body font; set here rather than in page CSS so mermaid measures labels
    // in the font they render in.
    // DOMPurify strips `target` by default (a reverse-tabnabbing guard that
    // modern browsers make redundant by implying noopener for _blank);
    // re-allow it so label links can open in a new tab.
    // Opaque edge-label background (the default has 0.8 alpha), so edges
    // passing behind a label are masked rather than showing through it.
    const edgeLabelBackground = lastThemeWasLight ? '#e8e8e8' : '#3c3f44';
    mermaid.initialize({
        startOnLoad: true, theme, securityLevel: 'loose',
        fontFamily: '"Open Sans", sans-serif',
        dompurifyConfig: { ADD_ATTR: ['target'] },
        themeVariables: { edgeLabelBackground },
    });

    // Simplest way to make mermaid re-render the diagrams in the new theme is via refreshing the page

    for (const darkTheme of darkThemes) {
        document.getElementById(darkTheme).addEventListener('click', () => {
            if (lastThemeWasLight) {
                window.location.reload();
            }
        });
    }

    for (const lightTheme of lightThemes) {
        document.getElementById(lightTheme).addEventListener('click', () => {
            if (!lastThemeWasLight) {
                window.location.reload();
            }
        });
    }
})();
